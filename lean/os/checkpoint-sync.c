/* Copyright (c) 2026 acorn contributors. MIT license.
 * Minimal POSIX boundary missing from Lean's standard handle API.
 * Lean flushes its handle before invoking this primitive and owns all
 * checkpoint bytes, exclusive creation, rename and cleanup decisions.
 * The pathname must continue to name the exclusively created regular file.
 */
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc != 2) {
        fputs("usage: checkpoint-sync FILE\n", stderr);
        return 2;
    }
    int fd = open(argv[1], O_WRONLY | O_NOFOLLOW | O_CLOEXEC);
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
    if (!S_ISREG(info.st_mode)) {
        fputs("checkpoint-sync requires a regular file\n", stderr);
        (void)close(fd);
        return 1;
    }
    int result;
    do {
        result = fsync(fd);
    } while (result < 0 && errno == EINTR);
    if (result < 0) {
        perror("checkpoint-sync fsync");
        (void)close(fd);
        return 1;
    }
    if (close(fd) != 0) {
        perror("checkpoint-sync close");
        return 1;
    }
    return 0;
}
