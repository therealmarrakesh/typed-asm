/* Runs snippets of machine code on this processor and prints what they did.
 *
 * Used only to regenerate tests/data/hardware.txt (see tests/Capture.lean).
 * It needs an x86-64 Linux machine. The tests themselves do not use it.
 *
 * Each input line is: the bytes to run in hex, then rax, rcx, rdx, rflags
 * and two memory words, all in hex. The bytes end with code that stores the
 * results at fixed addresses and jumps back here; that code is generated in
 * Tests/Hardware.lean, which is also where the addresses below come from.
 */
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define DATA 0x10000UL
#define BUFFER 0x10800UL
#define CODE 0x20000UL
#define IO 0x30000UL

static sigjmp_buf recover;
static void on_fault(int sig) { (void)sig; siglongjmp(recover, 1); }

/* Load the inputs, point rsp and rbx at the buffer, and jump to the snippet.
 * The snippet's trailing code restores rsp from IO+192 and jumps to IO+200. */
void enter(void);
__asm__(
    ".intel_syntax noprefix\n"
    ".globl enter\n"
    "enter:\n"
    "  push rbx\n  push rbp\n  push r12\n  push r13\n  push r14\n  push r15\n"
    "  mov qword ptr [0x300c0], rsp\n"
    "  lea rax, [rip + 1f]\n"
    "  mov qword ptr [0x300c8], rax\n"
    "  mov rax, qword ptr [0x30000]\n"
    "  mov rcx, qword ptr [0x30008]\n"
    "  mov rdx, qword ptr [0x30010]\n"
    "  xor esi, esi\n  xor edi, edi\n  xor r11d, r11d\n"
    "  mov rbx, 0x10800\n"
    "  mov r10, 2\n"
    "  push qword ptr [0x30018]\n"
    "  popfq\n"
    "  mov rsp, 0x10800\n"
    "  jmp qword ptr [0x300d0]\n"
    "1:\n"
    "  pop r15\n  pop r14\n  pop r13\n  pop r12\n  pop rbp\n  pop rbx\n"
    "  ret\n"
    ".att_syntax\n");

static void *map_at(unsigned long addr, int prot) {
    void *p = mmap((void *)addr, 4096, prot,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (p != (void *)addr) { perror("mmap"); exit(1); }
    return p;
}

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

int main(void) {
    uint64_t *data = map_at(DATA, PROT_READ | PROT_WRITE);
    uint8_t *code = map_at(CODE, PROT_READ | PROT_WRITE | PROT_EXEC);
    uint64_t *io = map_at(IO, PROT_READ | PROT_WRITE);

    /* A fault can arrive while rsp points into the buffer, so handle it elsewhere. */
    stack_t alt = { .ss_sp = malloc(1 << 16), .ss_size = 1 << 16, .ss_flags = 0 };
    sigaltstack(&alt, NULL);
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_fault;
    sa.sa_flags = SA_ONSTACK;
    sigaction(SIGFPE, &sa, NULL);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGILL, &sa, NULL);

    char *line = NULL;
    size_t cap = 0;
    while (getline(&line, &cap, stdin) > 0) {
        char *p = line;
        size_t n = 0;
        while (hexval(p[0]) >= 0 && hexval(p[1]) >= 0) {
            code[n++] = (uint8_t)(hexval(p[0]) * 16 + hexval(p[1]));
            p += 2;
        }
        unsigned long long v[6];
        if (sscanf(p, "%llx %llx %llx %llx %llx %llx", &v[0], &v[1], &v[2], &v[3], &v[4], &v[5]) != 6) {
            fprintf(stderr, "bad line\n");
            return 1;
        }
        memset(data, 0, 4096);
        uint64_t *buffer = (uint64_t *)BUFFER;
        buffer[0] = v[4];
        buffer[1] = v[5];
        io[0] = v[0]; io[1] = v[1]; io[2] = v[2]; io[3] = v[3];
        io[26] = CODE;
        if (sigsetjmp(recover, 1)) { puts("fault"); continue; }
        enter();
        uint64_t f = io[14];
        printf("ok %llx %llx %llx %llx %llx %llx %d%d%d%d %llx %llx %llx\n",
               (unsigned long long)io[8], (unsigned long long)io[9], (unsigned long long)io[10],
               (unsigned long long)io[11], (unsigned long long)io[12], (unsigned long long)io[13],
               (int)(f & 1), (int)((f >> 6) & 1), (int)((f >> 7) & 1), (int)((f >> 11) & 1),
               (unsigned long long)buffer[-1], (unsigned long long)buffer[0],
               (unsigned long long)buffer[1]);
    }
    return 0;
}
