"""Exact-rational independent ideal trajectory for josephCertifiedHorizonChecks.

Original dyadic model words vary in time. Scenario 0 has unit dynamics;
scenario 1 has a near-unit first component and a sign-reversing second.
Fraction evaluates ideal prediction/optimal update recursively from original
dense initialization. Only the seven checkpoint outputs round to binary64.
Run: python3 Kalman/Tests/JosephHorizonReference.py
"""

from fractions import Fraction as F

CHECKPOINTS = [0, 1, 2, 7, 31, 127, 256]


def model(scenario, t):
    f = [1.0, 1.0] if scenario == 0 else [1023 / 1024, -1.0]
    q = [1.0 + (t % 3) / 4, 1.0 + ((t + 1) % 3) / 4]
    r = [1.0 + ((t + 2) % 3) / 4, 1.0 + (t % 3) / 4]
    z = [1.0 if t % 4 < 2 else -1.0, float(t % 3 - 1)]
    return f, q, r, z


def references():
    for scenario in range(2):
        x, p = [F(1), F(-1)], [F(1), F(1.5)]
        for t in range(257):
            if t in CHECKPOINTS:
                yield list(map(float, [x[0], x[1], p[0], 0, 0, p[1]]))
            if t < 256:
                f, q, r, z = [[F(v) for v in row] for row in model(scenario, t)]
                a = [f[i]**2 * p[i] + q[i] for i in range(2)]
                y = [f[i] * x[i] for i in range(2)]
                x = [(r[i] * y[i] + a[i] * z[i]) / (a[i] + r[i]) for i in range(2)]
                p = [a[i] * r[i] / (a[i] + r[i]) for i in range(2)]


if __name__ == "__main__":
    for result in references():
        print("#[" + ", ".join(format(v, ".17g") for v in result) + "],")
