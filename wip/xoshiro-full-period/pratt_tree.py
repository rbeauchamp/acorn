import math
import random

ROOTS = [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721,
         59649589127497217, 5704689200685129054721]
BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def is_probable_prime(n):
    if n < 2:
        return False
    for p in BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def rho(n):
    if n % 2 == 0:
        return 2
    rng = random.Random(n)
    while True:
        c = rng.randrange(1, n)
        x = y = rng.randrange(2, n)
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d


def factor(n):
    if n == 1:
        return []
    if is_probable_prime(n):
        return [n]
    d = rho(n)
    return sorted(factor(d) + factor(n // d))


def root(p, qs):
    for a in range(2, 1000):
        if all(pow(a, (p - 1) // q, p) != 1 for q in qs):
            return a
    return None


def main():
    out = {}

    def go(p):
        if p < 1024 or p in out:
            return
        fs = factor(p - 1)
        qs = sorted(set(fs))
        out[p] = (root(p, qs), [(q, fs.count(q)) for q in qs])
        for q in qs:
            go(q)

    for p in ROOTS:
        go(p)
    for p in sorted(out):
        print(p, out[p])
    print("entries", len(out))


main()
