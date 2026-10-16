"""Original-binary64-word Fraction references for coupled prediction.

Run this file to regenerate the Lean reference rows. All arithmetic preceding
the final reference conversion is rational and independent of the dense kernel.
"""
from fractions import Fraction as F


def references():
    for dt in [.125, .25, 1.]:
        for a, b, c in [(1., .125, 1.5), (.5, -.25, 1.), (1.5, 1 / 7, 2.)]:
            for q0, q1 in [(.3125, .125), (1., 1.5)]:
                for x0, x1 in [(.1, -.2), (1., 1.)]:
                    d, aa, bb, cc, p, v, u, w = map(F, [dt, a, b, c, x0, x1, q0, q1])
                    yield [p + d * v, v, aa + 2 * d * bb + d * d * cc + u,
                           bb + d * cc, bb + d * cc, cc + w]


def tracking_references():
    """Independent scalar-innovation recursion, not a hard-coded fixed gain."""
    checkpoints = {0, 1, 2, 4, 8, 16, 32, 128, 1024}
    p, v = F(1, 8), F(-1, 2)
    a, b, c = F(1, 2), F(1, 4), F(1)
    measurements = [F(1, 2**24), F(-1, 2**24), F(0), F(1, 2**25)]
    for t in range(1025):
        if t in checkpoints:
            yield [p, v, a, b, b, c]
        if t == 1024:
            break
        pp, vv = p + v / 4, v
        aa, bb, cc = a + b / 2 + c / 16 + F(5, 16), b + c / 4, c + F(1, 8)
        s = aa + 1
        residual = measurements[t % 4] - pp
        p, v = pp + aa / s * residual, vv + bb / s * residual
        a, b, c = aa / s, bb / s, cc - bb * bb / s


if __name__ == '__main__':
    for row in references():
        print('  #[' + ', '.join(format(float(v), '.17g') for v in row) + '],')
