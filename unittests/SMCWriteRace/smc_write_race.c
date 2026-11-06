/*
 * Regression coverage for mach9#54: losing an RWX write during compilation.
 *
 * gated (default): deterministic PROTECTION-ORDER assertion, not a claim that
 * a guest store races publication. The compiler records the actual protection
 * of the opcode and modified immediate before publication, without waiting for
 * the test. It writes the result only after releasing the code-invalidation
 * mutex. The test then stores a new immediate and checks the callable code.
 * This fails the old late-trap protocol without a scheduling delay.
 * Iterations alternate a same-page function and a function whose mov opcode
 * is the last byte of a page and whose immediate is on the next page, both
 * pages belonging to the same executable interval.
 *
 * stress: probabilistic racing-store coverage, without a gate. The worker is
 * paused ONLY across VirtualProtect, then resumed BEFORE the store/check.
 *
 * Probe files are per-process. All payloads are little-endian uint64_t arrays
 * (the same layout for i686, x86_64 and the native compiler):
 *   want.<pid>  [GuestRIP, modified byte address, nonzero sequence]
 *   ready.<pid> [the three request fields, opcode protection, immediate
 *                protection, query duration in ns, code-lock duration in ns]
 * Missing/mismatched replies and failed protection queries are errors, never
 * successful schedules. ready.<pid>.error contains the request fields, failure
 * stage (1=no capture, 2=request read, 3=request delete, 4=result open,
 * 5=result write), and OS error. No compiler-side timeout or controller wait exists.
 * The guest's watchdog waits hold no FEX code-invalidation lock. Reported
 * durations are observed samples, not hard bounds or baseline overhead.
 *
 * Usage: smc_write_race.exe [gatedir] [iterations] [gated|stress]
 * Default directory: Z:/tmp/fex-smc-gate (must match FEX_SMC_TEST_GATE).
 * Defaults: 1000 gated / 5000 stress iterations. Exit status is a bitmask:
 * stale=2, timeout=4, protocol/protection/setup error=8, success=0.
 * Build: {i686,x86_64}-w64-mingw32-clang -O2 -static -o test.exe smc_write_race.c
 */
#include <windows.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char* pages;
static int (*volatile fn)(void);
static volatile LONG g_pause = 1;
static volatile LONG g_stop;
static volatile LONG g_want;
static HANDLE g_idle;
static HANDLE g_done;
static FILE* g_log;
static ULONGLONG g_t0;
/* Existing controller watchdog, not a JIT deadline. These waits never hold the
   code-invalidation mutex, and the compiler does not wait for this controller. */
static const DWORD TestWatchdogMs = 10000;

static void say(const char* fmt, ...) {
  va_list ap, copy;
  va_start(ap, fmt);
  va_copy(copy, ap);
  ULONGLONG ms = GetTickCount64() - g_t0;
  printf("smc| +%llu: ", (unsigned long long)ms);
  vprintf(fmt, ap);
  printf("\n");
  fflush(stdout);
  if (g_log) {
    fprintf(g_log, "smc| +%llu: ", (unsigned long long)ms);
    vfprintf(g_log, fmt, copy);
    fprintf(g_log, "\n");
    fflush(g_log);
  }
  va_end(copy);
  va_end(ap);
}

static int write_message(const char* path, const void* data, size_t size) {
  FILE* f = fopen(path, "wb");
  if (!f)
    return 0;
  int ok = fwrite(data, 1, size, f) == size;
  if (fclose(f) != 0)
    ok = 0;
  return ok;
}

static int read_message(const char* path, void* data, size_t size) {
  FILE* f = fopen(path, "rb");
  if (!f)
    return 0;
  int ok = fread(data, 1, size, f) == size;
  fclose(f);
  return ok;
}

static int wait_message(const char* path, void* data, size_t size, const char* error_path, const uint64_t request[3]) {
  ULONGLONG start = GetTickCount64();
  do {
    if (read_message(path, data, size))
      return 1;
    uint64_t error[5];
    if (read_message(error_path, error, sizeof(error)) && memcmp(error, request, 3 * sizeof(uint64_t)) == 0) {
      say("probe failure sequence=%llu stage=%llu os_error=%llu", (unsigned long long)error[2],
          (unsigned long long)error[3], (unsigned long long)error[4]);
      return -1;
    }
    Sleep(1);
  } while (GetTickCount64() - start < TestWatchdogMs);
  return 0;
}

static int pause_worker(void) {
  ResetEvent(g_idle);
  InterlockedExchange(&g_pause, 1);
  return WaitForSingleObject(g_idle, TestWatchdogMs) == WAIT_OBJECT_0;
}

static void resume_worker(void) { InterlockedExchange(&g_pause, 0); }

static DWORD __stdcall worker(void* arg) {
  (void)arg;
  while (!InterlockedCompareExchange(&g_stop, 0, 0)) {
    if (InterlockedCompareExchange(&g_pause, 0, 0)) {
      SetEvent(g_idle);
      Sleep(1);
      continue;
    }
    (void)fn();
    if (InterlockedCompareExchange(&g_want, 0, 0))
      SetEvent(g_done);
  }
  return 0;
}

static int reset_protection(void) {
  DWORD old;
  /* Both pages must be one RWX interval. No guest executes while they are RW. */
  return VirtualProtect(pages, 8192, PAGE_READWRITE, &old) &&
         VirtualProtect(pages, 8192, PAGE_EXECUTE_READWRITE, &old);
}

static void write_immediate(unsigned char* code, uint32_t value) {
  /* The same-page immediate is deliberately unaligned. A packed field keeps
     the single x86 DWORD store without making an invalid C alignment claim. */
  struct __attribute__((packed)) immediate { uint32_t value; };
  ((volatile struct immediate*)(code + 1))->value = value;
}

static int write_trapped(uint64_t protection) {
  return protection == PAGE_READONLY || protection == PAGE_EXECUTE_READ;
}

struct timing_sample {
  uint64_t query_ns;
  uint64_t lock_ns;
};

static int compare_time(const void* a, const void* b) {
  uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b;
  return (x > y) - (x < y);
}

static int report_timings(const struct timing_sample* samples, unsigned count) {
  uint64_t* values = malloc((size_t)count * sizeof(*values));
  if (!values && count)
    return 0;
  for (unsigned scenario = 0; scenario < 2; ++scenario) {
    for (unsigned metric = 0; metric < 2; ++metric) {
      size_t n = 0;
      for (unsigned i = scenario; i < count; i += 2)
        values[n++] = metric ? samples[i].lock_ns : samples[i].query_ns;
      if (!n)
        continue;
      qsort(values, n, sizeof(*values), compare_time);
      say("timing scenario=%s metric=%s n=%llu p50=%llu p95=%llu p99=%llu max=%llu",
          scenario ? "cross-page" : "same-page", metric ? "code_lock_ns" : "probe_ns",
          (unsigned long long)n, (unsigned long long)values[(n * 50 + 99) / 100 - 1],
          (unsigned long long)values[(n * 95 + 99) / 100 - 1], (unsigned long long)values[(n * 99 + 99) / 100 - 1],
          (unsigned long long)values[n - 1]);
    }
  }
  free(values);
  return 1;
}

int main(int argc, char** argv) {
  const char* dir = argc > 1 ? argv[1] : "Z:/tmp/fex-smc-gate";
  const char* mode = argc > 3 ? argv[3] : "gated";
  int stress = strcmp(mode, "stress") == 0;
  int iterations = argc > 2 ? atoi(argv[2]) : (stress ? 5000 : 1000);
  if ((!stress && strcmp(mode, "gated") != 0) || iterations <= 0) {
    fprintf(stderr, "usage: %s [gatedir] [positive iterations] [gated|stress]\n", argv[0]);
    return 8;
  }
  DWORD pid = GetCurrentProcessId();
  g_t0 = GetTickCount64();
  char want[560], ready[560], probe_error[580], logpath[640];
  snprintf(want, sizeof(want), "%s/want.%lu", dir, (unsigned long)pid);
  snprintf(ready, sizeof(ready), "%s/ready.%lu", dir, (unsigned long)pid);
  snprintf(probe_error, sizeof(probe_error), "%s.error", ready);
  snprintf(logpath, sizeof(logpath), "%s/exe.%s.%lu.log", dir, mode, (unsigned long)pid);
  g_log = fopen(logpath, "w");
  if (!g_log) {
    snprintf(logpath, sizeof(logpath), "c:/smc_write_race.%s.%lu.log", mode, (unsigned long)pid);
    g_log = fopen(logpath, "w");
  }
  say("start mode=%s iterations=%d dir=%s pid=%lu", mode, iterations, dir, (unsigned long)pid);

  struct timing_sample* samples = stress ? NULL : calloc((size_t)iterations, sizeof(*samples));
  if (!stress && !samples) {
    say("timing allocation failed");
    return 8;
  }
  unsigned measured = 0;
  pages = VirtualAlloc(NULL, 8192, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  if (!pages) {
    say("VirtualAlloc failed err=%lu", (unsigned long)GetLastError());
    return 8;
  }
  const unsigned offsets[2] = {0, 4095};
  for (int j = 0; j < 2; ++j) {
    unsigned char* code = pages + offsets[j];
    code[0] = 0xB8; /* mov eax, imm32 */
    write_immediate(code, 0);
    code[5] = 0xC3; /* ret */
  }
  fn = (int (*)(void))pages;
  g_idle = CreateEvent(NULL, FALSE, FALSE, NULL);
  g_done = CreateEvent(NULL, FALSE, FALSE, NULL);
  HANDLE wt = (g_idle && g_done) ? CreateThread(NULL, 0, worker, NULL, 0, NULL) : NULL;
  if (!wt) {
    say("worker/event creation failed err=%lu", (unsigned long)GetLastError());
    return 8;
  }
  unsigned stale = 0, timeouts = 0, checked = 0, errors = 0;
  for (int i = 1; i <= iterations; ++i) {
    if (!pause_worker()) {
      ++timeouts;
      break;
    }
    unsigned char* code = pages + offsets[(i - 1) & 1];
    fn = (int (*)(void))code;
    if (!reset_protection()) {
      say("VirtualProtect failed err=%lu", (unsigned long)GetLastError());
      ++errors;
      break;
    }
    if (stress) {
      /* This ordering is intentional: the worker can capture the old bytes
         concurrently with the store. Pausing through the store erases the race. */
      resume_worker();
      write_immediate(code, (unsigned)i);
      unsigned r = (unsigned)fn();
      ++checked;
      if (r != (unsigned)i) {
        ++stale;
        if (stale <= 5)
          say("STALE stress iteration=%d wrote=%u got=%u", i, (unsigned)i, r);
      }
      continue;
    }

    DeleteFileA(want);
    DeleteFileA(ready);
    DeleteFileA(probe_error);
    uint64_t request[3] = {(uint64_t)(uintptr_t)code, (uint64_t)(uintptr_t)(code + 1), (uint64_t)i};
    if (!write_message(want, request, sizeof(request))) {
      say("cannot arm probe iteration=%d err=%lu", i, (unsigned long)GetLastError());
      ++errors;
      break;
    }
    ResetEvent(g_done);
    InterlockedExchange(&g_want, 1);
    resume_worker();
    uint64_t reply[7];
    int received = wait_message(ready, reply, sizeof(reply), probe_error, request);
    if (received <= 0 || memcmp(reply, request, sizeof(request)) != 0) {
      say("missing/mismatched target sample iteration=%d target=%p", i, code);
      if (received == 0)
        ++timeouts;
      else
        ++errors;
      break;
    }
    samples[measured].query_ns = reply[5];
    samples[measured++].lock_ns = reply[6];
    int trapped = write_trapped(reply[3]) && write_trapped(reply[4]);
    if (!trapped) {
      say("UNTRAPPED before publication iteration=%d crosspage=%d opcode_prot=%llx immediate_prot=%llx",
          i, (i - 1) & 1, (unsigned long long)reply[3], (unsigned long long)reply[4]);
      ++errors;
    }
    if (WaitForSingleObject(g_done, TestWatchdogMs) != WAIT_OBJECT_0) {
      say("worker did not return iteration=%d", i);
      ++timeouts;
      break;
    }
    InterlockedExchange(&g_want, 0);
    /* The host sampled before publication and returned the record after unlock.
       This store checks invalidation; stress mode separately races the store. */
    write_immediate(code, (unsigned)i);
    unsigned r = (unsigned)fn();
    ++checked;
    if (r != (unsigned)i) {
      ++stale;
      if (stale <= 5)
        say("STALE gated iteration=%d wrote=%u got=%u", i, (unsigned)i, r);
    }
    if (!trapped)
      break;
  }

  DeleteFileA(want);
  InterlockedExchange(&g_stop, 1);
  resume_worker();
  int stopped = WaitForSingleObject(wt, TestWatchdogMs) == WAIT_OBJECT_0;
  if (!stopped) {
    say("worker shutdown timed out");
    ++timeouts;
  }
  CloseHandle(wt);
  /* Do not free a timed-out worker's code or event handles underneath it. */
  if (stopped) {
    CloseHandle(g_idle);
    CloseHandle(g_done);
    VirtualFree(pages, 0, MEM_RELEASE);
  }
  if (!stress && !report_timings(samples, measured)) {
    say("timing report allocation failed");
    ++errors;
  }
  free(samples);
  say("summary mode=%s iterations=%d checked=%u stale=%u probe_timeouts=%u errors=%u",
      mode, iterations, checked, stale, timeouts, errors);
  say(stress ? "stress is probabilistic racing-store coverage" :
               "gated samples protection before publication without waiting in the compiler; timings are observed, not bounds");
  if (g_log)
    fclose(g_log);
  return (stale ? 2 : 0) | (timeouts ? 4 : 0) | (errors ? 8 : 0);
}
