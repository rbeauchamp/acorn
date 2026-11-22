import sys

M = (1 << 64) - 1


def rotl(x, k):
    return ((x << k) | (x >> (64 - k))) & M


def nxt(s):
    s0, s1, s2, s3 = s
    t = (s1 << 17) & M
    s2 ^= s0
    s3 ^= s1
    s1 ^= s2
    s0 ^= s3
    s2 ^= t
    s3 = rotl(s3, 45)
    return (s0, s1, s2, s3)


def pack(s):
    return s[0] | (s[1] << 64) | (s[2] << 128) | (s[3] << 192)


def unpack(n):
    return (n & M, (n >> 64) & M, (n >> 128) & M, (n >> 192) & M)


def berlekamp_massey(bits):
    n = len(bits)
    c = 1
    b = 1
    L = 0
    m = 1
    for i in range(n):
        d = bits[i]
        for j in range(1, L + 1):
            if (c >> j) & 1:
                d ^= bits[i - j]
        if d == 0:
            m += 1
        elif 2 * L <= i:
            t = c
            c ^= b << m
            L = i + 1 - L
            b = t
            m = 1
        else:
            c ^= b << m
            m += 1
    return c, L


def reverse_poly(c, L):
    r = 0
    for j in range(L + 1):
        if (c >> j) & 1:
            r |= 1 << (L - j)
    return r


def peval(f, v):
    acc = 0
    for i in reversed(range(f.bit_length())):
        acc = pack(nxt(unpack(acc)))
        if (f >> i) & 1:
            acc ^= v
    return acc


def main():
    v0 = 1
    seq = []
    s = unpack(v0)
    for _ in range(1024):
        seq.append(s[0] & 1)
        s = nxt(s)
    c, L = berlekamp_massey(seq)
    p = reverse_poly(c, L)
    print("degree", L)
    print("p", hex(p))
    print("weight", bin(p).count("1"))
    print("annihilates v0", peval(p, v0) == 0)
    for k in range(64):
        v = 1 << (k * 4 + 3)
        assert peval(p, v) == 0
    print("annihilates 64 basis vectors: True")


main()
