"""Original-word exact-rational prediction/full-step oracle.

Cases exercise incoming invariant boundaries, reset/sign-changing dynamics,
non-dyadic transition/measurement words, and both noise endpoints. The native
algorithm's multiplication, addition, gain solve, and Joseph schedule are not
replayed. Fraction evaluates the scalar ideal equations; only outputs round.
Run: python3 Kalman/Tests/JosephStepReference.py
"""

from fractions import Fraction as F

# f0,f1,p0,p1,q0,q1,r0,r1,x0,x1,z0,z1
CASES = [
    [1.0, 1.0, 7/16, 13/8, 1.0, 1.5, 1.0, 1.5, 9/8, -9/8, 1.0, -1.0],
    [-1.0, 1.0, 13/8, 7/16, 1.5, 1.0, 1.5, 1.0, 9/8, -9/8, -1.0, 1.0],
    [0.0, -0.0, 7/16, 13/8, 1.0, 1.5, 1.0, 1.5, -9/8, 9/8, 0.0, 1.0],
    [1/3, -1/3, 13/8, 7/16, 1.25, 1.5, 1.25, 1.25, 9/8, -9/8, 1/3, -1/3],
    [1023/1024, -1.0, 7/16, 13/8, 1.5, 1.0, 1.5, 1.0, 1/3, -9/8, -1.0, 0.5],
    [-0.0, 1023/1024, 13/8, 13/8, 1.0, 1.25, 1.25, 1.5, -9/8, 9/8, 0.0, 1.0],
    [-1/3, 1023/1024, 7/16, 7/16, 1.5, 1.5, 1.0, 1.5, 9/8, -9/8, 1.0, 0.0],
    [1.0, -1.0, 13/8, 13/8, 1.5, 1.5, 1.5, 1.5, -9/8, 9/8, 1.0, -1.0],
]


def references():
    for row in CASES:
        f, p, q, r, x, z = [[F(v) for v in row[i:i+2]] for i in range(0, 12, 2)]
        a = [f[i]**2 * p[i] + q[i] for i in range(2)]
        y = [f[i] * x[i] for i in range(2)]
        pp = [a[i] * r[i] / (a[i] + r[i]) for i in range(2)]
        xx = [(r[i] * y[i] + a[i] * z[i]) / (a[i] + r[i]) for i in range(2)]
        yield list(map(float, [y[0], y[1], a[0], 0, 0, a[1], xx[0], xx[1], pp[0], 0, 0, pp[1]]))


if __name__ == "__main__":
    for result in references():
        print("#[" + ", ".join(format(v, ".17g") for v in result) + "],")
