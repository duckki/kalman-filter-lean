"""Manual independent oracle for observableHorizonChecks.

Run: python3 Kalman/Tests/ObservableHorizonReference.py
All native input constants are exact dyadics. Standard-library Decimal evaluates
an independent ideal diagonal recursion at 120 and 160 digits. Rounded reference
words must agree. This oracle supplements local accuracy/invariance proofs;
it does not prove accumulated trajectory error.
"""

from decimal import Decimal as D, localcontext


def generate(precision):
    with localcontext() as ctx:
        ctx.prec = precision
        p = [D(5) / 4, D(3) / 2]
        x = [D(1), -D(1)]
        checkpoints = []
        for t in range(256):
            f = [D(1) if t % 3 == 0 else D(1023) / 1024,
                 [D(1), -D(1), D(255) / 256, -D(1023) / 1024][t % 4]]
            q = [D(1), D(3) / 2] if t % 2 == 0 else [D(3) / 2, D(1)]
            r = [D(3) / 2, D(1)] if t % 3 == 0 else [D(1), D(3) / 2]
            z = [D(1), -D(1)] if t % 2 == 0 else [-D(1), D(1)]
            for i in range(2):
                prior = f[i] * f[i] * p[i] + q[i]
                predicted = f[i] * x[i]
                k = prior / (prior + r[i])
                variance = prior * r[i] / (prior + r[i])
                joseph = (1 - k) ** 2 * prior + k ** 2 * r[i]
                assert abs(joseph - variance) < D("1e-110")
                x[i] = r[i] / (prior + r[i]) * predicted + k * z[i]
                p[i] = variance
            if t + 1 in {1, 2, 3, 8, 32, 128, 256}:
                checkpoints.append((t + 1, tuple(map(float, p)), tuple(map(float, x))))
        return checkpoints


if __name__ == "__main__":
    reference = generate(120)
    assert reference == generate(160)
    for t, p, x in reference:
        cov = ", ".join(format(v, ".17g") for v in (p[0], 0.0, 0.0, p[1]))
        mean = ", ".join(format(v, ".17g") for v in x)
        print(f"({t}, #[{cov}], #[{mean}]),")
    print("120/160-digit rounded references agree.")
