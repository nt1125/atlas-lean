"""
peo_insufficiency.py — a 2-path of 5 triangles on which no fill-free ordering is clean
Tests Remark 4.6: an SPD realization with zero clean simplicial vertices, so that a pure
PEO strategy, which never creates fill, fails.

The pattern is the 2-path strip on 0..6 (edges {i,i+1} and {i,i+2}), whose triangles are
{i,i+1,i+2}, i = 0..4. Its simplicial vertices are the ends 0 and 6. The matrix below makes
each end zero the opposite edge of its triangle: A00*A12 = A01*A02 and A66*A45 = A64*A65
(Definition 2.19), so neither end is a clean pivot at the empty level. Arithmetic is exact
(fractions), so every zero test is exact. The script checks that the matrix is SPD with this
pattern, then runs all 7! orderings through the elimination game and the Schur updates of
Definition 2.6: an ordering is clean (Definition 2.24) if every position committed to L is
nonzero, and it is a perfect elimination ordering (PEO) if it creates no fill.
"""
import itertools
from fractions import Fraction as F

N = 7
h = F(1, 2)
A = [[2, 1, 1, 0, 0, 0, 0],
     [1, 3, h, h, 0, 0, 0],
     [1, h, 3, h, h, 0, 0],
     [0, h, h, 3, h, h, 0],
     [0, 0, h, h, 3, h, 1],
     [0, 0, 0, h, h, 3, 1],
     [0, 0, 0, 0, 1, 1, 2]]
A = [[F(x) for x in row] for row in A]
STRIP = {frozenset((i, i + d)) for d in (1, 2) for i in range(N - d)}

def is_spd(M):
    """Symmetric, and every pivot of Gaussian elimination in natural order is positive."""
    if any(M[i][j] != M[j][i] for i in range(N) for j in range(N)):
        return False
    M = [row[:] for row in M]
    for p in range(N):
        if M[p][p] <= 0:
            return False
        for j in range(p + 1, N):
            f = M[j][p] / M[p][p]
            for k in range(p, N):
                M[j][k] -= f * M[p][k]
    return True

def eliminate(order):
    """Run `order` through the elimination game and the Schur updates.
    Returns (clean, fill_free)."""
    M = {j: {k: A[j][k] for k in range(N)} for j in range(N)}
    adj = {v: {u for u in range(N) if u != v and A[u][v] != 0} for v in range(N)}
    clean, fill_free = True, True
    for p in order:
        if any(M[p][x] == 0 for x in adj[p]):   # a committed position of L is zero
            clean = False
        nbrs = adj[p]
        for a, b in itertools.combinations(nbrs, 2):
            if b not in adj[a]:                 # the pivot creates a fill edge
                fill_free = False
                adj[a].add(b); adj[b].add(a)
        for v in nbrs:
            adj[v].discard(p)
        del adj[p]
        rest = [v for v in M if v != p]
        M = {j: {k: M[j][k] - M[j][p] * M[k][p] / M[p][p] for k in rest} for j in rest}
    return clean, fill_free

pattern = {frozenset((i, j)) for i in range(N) for j in range(i + 1, N) if A[i][j] != 0}
assert is_spd(A), "matrix is not SPD"
assert pattern == STRIP, "pattern is not the 2-path of 5 triangles"
nbr = {v: {u for u in range(N) if frozenset((u, v)) in pattern} for v in range(N)}
simplicial = [v for v in range(N)
              if all(frozenset((a, b)) in pattern for a, b in itertools.combinations(nbr[v], 2))]
# C_v at the empty level: pairs {j,k} with A_vv A_jk = A_vj A_vk (Definition 2.19)
clean_simplicial = [v for v in simplicial
                    if not any(A[v][v] * A[j][k] == A[v][j] * A[v][k]
                               for j, k in itertools.combinations(range(N), 2)
                               if v not in (j, k) and frozenset((j, k)) in pattern)]

orders = clean_count = peo_count = clean_peo_count = 0
for order in itertools.permutations(range(N)):
    orders += 1
    clean, fill_free = eliminate(order)
    clean_count += clean
    peo_count += fill_free
    clean_peo_count += clean and fill_free

print(f"Matrix is SPD with the pattern of the 2-path of 5 triangles on {N} vertices")
print(f"Simplicial vertices: {simplicial} (expected [0, 6])")
print(f"Clean simplicial vertices at the empty level: {len(clean_simplicial)} (expected 0)")
print(f"Enumerated {orders} orderings: {peo_count} perfect elimination orderings, "
      f"{clean_peo_count} of them clean (expected 0)")
print(f"Clean orderings: {clean_count} (expected > 0; each creates fill)")
