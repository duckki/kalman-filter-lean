"""Original-binary64-word Fraction references for coupled prediction.

Run this file to regenerate prediction rows, or pass --tracking for tracking
rows. All arithmetic preceding final conversion is rational and independent
of the dense kernel.
"""
import argparse
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


def transient_references(robust=False):
    """Nonstationary covariance, using exact original-word scalar equations."""
    for sign in [-1, 1]:
        p, v = F(1, 8), F(-1, 2)
        a, b, c = F(1, 2) + sign * F(1, 4096), F(1, 4), F(1) + sign * F(1, 4096)
        measurements = [F(1, 2**24), F(-1, 2**24), F(0), F(1, 2**25)]
        for t in range(17):
            if t in {0, 1, 2, 4, 8, 16}:
                yield [p, v, a, b, b, c]
            if t == 16:
                break
            theta = F(1, 2**21)
            choices = [(F(1, 4)-theta, F(5, 16)+theta, F(1, 8)-theta, F(1)),
                       (F(1, 4)+theta, F(5, 16)-theta, F(1, 8)+theta, F(1)+theta),
                       (F(1, 4), F(5, 16), F(1, 8), F(1)+theta),
                       (F(1, 4)+theta, F(5, 16)+theta, F(1, 8)+theta, F(1))]
            dt, q0, q1, rr = choices[t % 4] if robust else (F(1, 4), F(5, 16), F(1, 8), F(1))
            pp, vv = p + dt * v, v
            aa, bb, cc = a + 2 * dt * b + dt * dt * c + q0, b + dt * c, c + q1
            innovation = aa + rr
            residual = measurements[t % 4] - pp
            p, v = pp + aa / innovation * residual, vv + bb / innovation * residual
            a, b, c = aa * rr / innovation, bb * rr / innovation, cc - bb * bb / innovation



if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tracking', action='store_true', help='emit tracking checkpoints')
    parser.add_argument('--transient', action='store_true', help='emit covariance-transient checkpoints')
    parser.add_argument('--robust', action='store_true', help='emit varying-parameter transient checkpoints')
    args = parser.parse_args()
    rows = transient_references(True) if args.robust else transient_references() if args.transient else tracking_references() if args.tracking else references()
    for row in rows:
        print('  #[' + ', '.join(format(float(v), '.17g') for v in row) + '],')
