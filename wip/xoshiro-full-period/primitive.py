P = 0x10003c03c3f3ecb1904b4edcf26259f850280002bcefd1a5e9d116f2bb0f0f001
D = 256
N = (1 << 256) - 1
PRIMES = [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721,
          59649589127497217, 5704689200685129054721]


def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def pmod(a, p=P):
    while a.bit_length() > D:
        a ^= p << (a.bit_length() - 1 - D)
    return a


def powx(e):
    y = 1
    for i in reversed(range(e.bit_length())):
        y = pmod(clmul(y, y))
        if (e >> i) & 1:
            y = pmod(y << 1)
    return y


def is_prime_small(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def factor(n):
    fs = []
    d = 2
    while d * d <= n and d < 10 ** 7:
        while n % d == 0:
            fs.append(d)
            n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs


def main():
    prod = 1
    for q in PRIMES:
        prod *= q
    print("product equals N", prod == N)
    y = 2
    for _ in range(256):
        y = pmod(clmul(y, y))
    print("x^(2^256) mod p == x", y == 2)
    for q in PRIMES:
        r = powx(N // q)
        print(q, "x^(N/q) mod p != 1", r != 1)
    for q in PRIMES[-3:]:
        print(q, "q-1 factors", factor(q - 1))


main()
