"""Manual high-precision oracle for originalInputHorizonChecks.

Run: python3 Kalman/Tests/HorizonReference.py
All input constants are exact dyadics. Standard-library Decimal at 120 digits
evaluates the ideal two-state Joseph recursion, separately checks agreement
with its subtractive identity, and prints the fixed Lean reference table.
The table is a regression oracle; it does not replace the Lean accuracy proof.
"""

from decimal import Decimal as D, localcontext


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def neg(a):
    return [[-v for v in row] for row in a]


def transpose(a):
    return list(map(list, zip(*a)))


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def inverse2(a):
    det = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    assert det > 0
    return [[a[1][1] / det, -a[0][1] / det],
            [-a[1][0] / det, a[0][0] / det]]


def generate(precision=120, transition_denominator=8):
    with localcontext() as ctx:
        ctx.prec = precision
        d = transition_denominator
        f = [[D(1) / d, D(1) / (2 * d)], [-D(1) / (4 * d), D(1) / d]]
        h = [[D(1) / 64, -D(1) / 128], [D(1) / 256, D(1) / 64]]
        q0 = [[D(1), D(1) / 4], [D(1) / 4, D(3) / 2]]
        q1 = [[D(3) / 2, -D(1) / 4], [-D(1) / 4, D(1)]]
        identity = [[D(1), D(0)], [D(0), D(1)]]
        p = q0
        mean = [[D(1) / 4], [-D(3) / 4]]
        checkpoints = {1, 2, 3, 8, 32, 128, 256}
        for t in range(256):
            q = q0 if t % 2 == 0 else q1
            r = q1 if t % 3 == 0 else q0
            z = [[D(1)], [-D(1)]] if t % 2 == 0 else [[-D(1)], [D(1)]]
            prior = add(mul(mul(f, p), transpose(f)), q)
            predicted_mean = mul(f, mean)
            s = add(mul(mul(h, prior), transpose(h)), r)
            k = mul(mul(prior, transpose(h)), inverse2(s))
            mean = add(predicted_mean, mul(k, add(z, neg(mul(h, predicted_mean)))))
            w = add(identity, neg(mul(k, h)))
            joseph = add(mul(mul(w, prior), transpose(w)), mul(mul(k, r), transpose(k)))
            subtractive = add(prior, neg(mul(mul(k, h), prior)))
            assert max(abs(joseph[i][j] - subtractive[i][j])
                       for i in range(2) for j in range(2)) < D("1e-110")
            p = joseph
            if t + 1 in checkpoints:
                cov = ", ".join(format(float(p[i][j]), ".17g")
                                for i in range(2) for j in range(2))
                mu = ", ".join(format(float(mean[i][0]), ".17g") for i in range(2))
                print(f"({t + 1}, #[{cov}], #[{mu}]),")


if __name__ == "__main__":
    generate()
