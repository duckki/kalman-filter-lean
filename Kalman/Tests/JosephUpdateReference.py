"""Exact original-input optimal-update oracle for josephCompleteUpdateChecks.

Fraction evaluates scalar posterior mean and variance. Only final references
are rounded; native code forms its own rounded gain and Joseph congruences.
Run: python3 Kalman/Tests/JosephUpdateReference.py
"""

from fractions import Fraction as F


def references():
    for p0 in [15 / 16, 13 / 4]:
        for p1 in [15 / 16, 13 / 4]:
            for r0 in [1.0, 1.5]:
                for r1 in [1.0, 1.5]:
                    for x in [-19 / 16, 19 / 16]:
                        for z in [-1.0, 1.0]:
                            p, r = [F(p0), F(p1)], [F(r0), F(r1)]
                            means = [(r[i] * F(x if i == 0 else -x)
                                      + p[i] * F(z if i == 0 else -z)) / (p[i] + r[i])
                                     for i in range(2)]
                            variances = [p[i] * r[i] / (p[i] + r[i]) for i in range(2)]
                            yield [float(means[0]), float(means[1]), float(variances[0]),
                                   0.0, 0.0, float(variances[1])]


if __name__ == "__main__":
    for result in references():
        print("#[" + ", ".join(format(v, ".17g") for v in result) + "],")
