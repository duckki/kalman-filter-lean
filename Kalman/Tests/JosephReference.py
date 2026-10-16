"""Exact rational oracle for josephStoredInputChecks.

Run: python3 Kalman/Tests/JosephReference.py
Interpret each input binary64 word exactly. Evaluate the expanded Joseph
polynomial, rather than the native congruence-product schedule, using Fraction.
Only the final reference entries are rounded to binary64. These references
supplement the covariance-kernel proof, not a computed-gain or horizon theorem.
"""

from fractions import Fraction as F


def references():
    gains = [
        [0.0, -0.0, 0.0, 0.0],
        [1 / 3, 0.0, 0.0, -1 / 3],
        [1 / 3, -1 / 3, 1 / 3, 1 / 3],
        [float.fromhex("0x0.0000000000001p-1022"), 0.0, -0.0, 0.125],
        [1.0, -1.0, 1.0, 1.0],
    ]
    observations = [
        [0.0, -0.0, 0.0, 0.0],
        [1 / 64, 0.0, -0.0, -1 / 64],
        [1 / 64, -1 / 64, 1 / 64, 1 / 64],
        [1.0, 0.0, 0.0, 1.0],
    ]
    for p0 in [1.0, 2.0]:
        p = list(map(F, [p0, 0.25, 0.25, 1.5]))
        r = list(map(F, [1.5, -0.25, -0.25, 1.0]))
        for obs in observations:
            h = list(map(F, obs))
            for gain in gains:
                k = list(map(F, gain))
                out = []
                for i in range(2):
                    for j in range(2):
                        v = p[2 * i + j]
                        for a in range(2):
                            for b in range(2):
                                v -= k[2 * i + a] * h[2 * a + b] * p[2 * b + j]
                                v -= p[2 * i + b] * h[2 * a + b] * k[2 * j + a]
                                v += k[2 * i + a] * r[2 * a + b] * k[2 * j + b]
                                for c in range(2):
                                    for d in range(2):
                                        v += (k[2 * i + a] * h[2 * a + c]
                                              * p[2 * c + d] * h[2 * b + d]
                                              * k[2 * j + b])
                        out.append(float(v))
                yield out


if __name__ == "__main__":
    for result in references():
        print("#[" + ", ".join(format(v, ".17g") for v in result) + "],")
