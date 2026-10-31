/* Copyright (c) 2026 acorn contributors. MIT license.
 * Minimal file-sync boundary missing from Lean's standard handle API.
 * Lean flushes its handle before invoking this primitive and owns all
 * checkpoint bytes, exclusive creation, rename and cleanup decisions.
 * A file pathname must continue to name the exclusively created regular file;
 * a directory pathname must continue to name the directory holding its entry.
 * lean/Acorn/Host/Checkpoint/IO.lean states what each path here establishes.
 * The path shared with other platforms uses only names POSIX.1-2008 defines
 * outside its XSI option, since the merge gate compiles on macOS only. Under
 * the build flags glibc's <sys/stat.h> alone hides S_IFMT; <fcntl.h> shows it.
 */
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

/* fsync on Apple platforms stops at the drive (fsync(2)), so a feature macro
 * that hid the flush request would silently weaken every save. */
#if defined(__APPLE__) && !defined(F_FULLFSYNC)
#error "checkpoint-sync requires F_FULLFSYNC on Apple platforms"
#endif

static int sync_to_device(int fd) {
    int result;
    do {
        result = fsync(fd);
    } while (result < 0 && errno == EINTR);
    return result;
}

#ifdef F_FULLFSYNC
/* fcntl(2) lists no error for F_FULLFSYNC and implements it per file system.
 * ENOTTY, ENOTSUP and EINVAL are the errors by which XNU itself recognizes a
 * file system lacking the request, when it promotes F_BARRIERFSYNC
 * (bsd/kern/kern_descrip.c, xnu-12377.121.6, lines 3982-3983). Every other
 * error, EIO included, is a failed flush that a later fsync could hide. */
static int sync_descriptor(int fd) {
    int result;
    do {
        result = fcntl(fd, F_FULLFSYNC, 0);
    } while (result == -1 && errno == EINTR);
    if (result != -1) {
        return 0;
    }
    if (errno != ENOTTY && errno != ENOTSUP && errno != EINVAL) {
        return -1;
    }
    if (sync_to_device(fd) != 0) {
        return -1;
    }
    fputs("checkpoint-sync: file system lacks F_FULLFSYNC; used fsync, which stops "
          "at the drive, so a power loss can lose this save and, if the image's own "
          "sync took this path, the image it replaced\n", stderr);
    return 0;
}
#else
static int sync_descriptor(int fd) {
    return sync_to_device(fd);
}
#endif

int main(int argc, char **argv) {
    int flags;
    int want_directory;
    if (argc == 3 && strcmp(argv[1], "file") == 0) {
        flags = O_WRONLY | O_NOFOLLOW | O_CLOEXEC;
        want_directory = 0;
    } else if (argc == 3 && strcmp(argv[1], "directory") == 0) {
        /* No O_NOFOLLOW: a parent may be reached through a link (/tmp on macOS),
         * and the entry to persist lies in the directory it resolves to. */
        flags = O_RDONLY | O_DIRECTORY | O_CLOEXEC;
        want_directory = 1;
    } else {
        fputs("usage: checkpoint-sync file|directory PATH\n", stderr);
        return 2;
    }
    int fd = open(argv[2], flags);
    if (fd < 0) {
        perror("checkpoint-sync open");
        return 1;
    }
    struct stat info;
    if (fstat(fd, &info) != 0) {
        perror("checkpoint-sync stat");
        (void)close(fd);
        return 1;
    }
    if (want_directory ? !S_ISDIR(info.st_mode) : !S_ISREG(info.st_mode)) {
        fputs("checkpoint-sync target has the wrong file type\n", stderr);
        (void)close(fd);
        return 1;
    }
    if (sync_descriptor(fd) != 0) {
        perror("checkpoint-sync flush");
        (void)close(fd);
        return 1;
    }
    if (close(fd) != 0) {
        perror("checkpoint-sync close");
        return 1;
    }
    return 0;
}
