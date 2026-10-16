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


if __name__ == '__main__':
    for row in references():
        print('  #[' + ', '.join(format(float(v), '.17g') for v in row) + '],')
