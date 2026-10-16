"""Exact rational gain oracle for josephComputedGainChecks.

Interpret the original finite binary64 prior/noise entries exactly. Evaluate
p/(p+r) with Fraction and round only the final reference entries. The native
filter instead forms rounded matrix products and sums and runs an LDL solve.
Run: python3 Kalman/Tests/JosephGainReference.py
"""

from fractions import Fraction as F


def references():
    priors = [15 / 16, 4 / 3, 2.0, 13 / 4]
    noises = [1.0, 4 / 3, 1.5]
    for p0 in priors:
        for p1 in priors:
            for r0 in noises:
                for r1 in noises:
                    yield [float(F(p0) / (F(p0) + F(r0))), 0.0, 0.0,
                           float(F(p1) / (F(p1) + F(r1)))]


if __name__ == "__main__":
    for result in references():
        print("#[" + ", ".join(format(v, ".17g") for v in result) + "],")
