# For odd h, which (d,d') (nonzero mod h) give a rational Sigma4 = z^{2d}+z^{-2d}+z^{2d'}+z^{-2d'} ?  (expect values {-2,-1} only)
import math
import numpy as np
from collections import Counter
vals = Counter()
for h in range(3, 202, 2):
    embs = np.array([j for j in range(1, h) if math.gcd(j, h) == 1])
    C = 2 * np.cos(4 * np.pi * np.outer(np.arange(h), embs) / h)   # row d: z^{2d}+z^{-2d} at all embeddings
    for d in range(1, h):
        for dp in range(d, h):
            v = C[d] + C[dp]
            if np.ptp(v) < 1e-9: vals[(round(v[0], 6))] += 1
print("rational Sigma4 values (h odd <= 201):", dict(vals))
