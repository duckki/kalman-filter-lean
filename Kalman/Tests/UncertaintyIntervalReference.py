"""Independent high-precision ideal endpoints for original binary64 input words.

Print Lean rows: mean, variance, covariance allowance, mean allowance, multiplier,
then the ideal lower/upper endpoints rounded outward by one binary64 neighbor.
These references are regression data, not proof witnesses.
"""
import math
import struct
from decimal import Decimal, localcontext


def word(x):
    return f"Float.ofBits 0x{struct.unpack('>Q', struct.pack('>d', x))[0]:016x}"


def references():
    tiny = math.ulp(0.0)
    cases = [(0., 0., 0., 0., 0.), (-0., -0., 0., -0., 8.),
             (tiny, tiny, tiny, tiny, tiny)]
    cases += [(m, v, c, e, k)
              for m in (-1., 0., 1.)
              for v, c, e, k in ((2., 1., 2., 8.), (.5, 0., 2.**-29, 3.),
                                 (1., 0., 0., 1.), (0., 0., 0., 8.),
                                 (math.nextafter(1., 0.), tiny, tiny, 8.))]
    cases += [(0.25, 0.0625, 0., 0., 1.),
              (-0.25, 0.0625, 0., 0., 1.),
              (1., math.nextafter(2., 0.), math.nextafter(1., 0.), 2., 8.)]
    with localcontext() as ctx:
        ctx.prec = 200
        for case in cases:
            m, v, c, e, k = map(Decimal.from_float, case)
            radius = k * (v + c).sqrt() + e
            lo = math.nextafter(float(m - radius), -math.inf)
            hi = math.nextafter(float(m + radius), math.inf)
            yield case + (lo, hi)


if __name__ == '__main__':
    print('  #[')
    rows = list(references())
    for i, row in enumerate(rows):
        print('    #[' + ', '.join(map(word, row)) + ']' + (',' if i + 1 < len(rows) else ''))
    print('  ]')
