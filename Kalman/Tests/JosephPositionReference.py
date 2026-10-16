"""Independent Fraction references for 72 checked position-only Joseph updates.

Interpret every original binary64 word exactly, then use the scalar innovation
and optimal posterior equations. Only the final expected values round to Float.
Run: python3 Kalman/Tests/JosephPositionReference.py
"""
from fractions import Fraction as F


def references():
    for a, c in [(1., 2.), (2., 1.), (1.5, 1.5)]:
        for b in [-.25, 0., 1 / 7]:
            for r in [1., 1.5]:
                for x in [(1., -1.), (-.1, .2)]:
                    for z in [-1., 1.]:
                        aa, bb, cc, rr, x0, x1, zz = map(F, [a, b, c, r, *x, z])
                        s = aa + rr
                        yield [x0 + aa / s * (zz - x0), x1 + bb / s * (zz - x0),
                               aa * rr / s, bb * rr / s, bb * rr / s, cc - bb**2 / s]


if __name__ == '__main__':
    for row in references():
        print('#[' + ', '.join(format(float(v), '.17g') for v in row) + '],')
