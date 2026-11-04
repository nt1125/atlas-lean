"""
fixed_ordering_witnesses.py — patterns of Theorem 4.8 on which no fixed ordering is clean
Tests Remark 4.9: for the triangle K3, and for the one-triangle pattern E on five vertices,
every ordering fixed in advance is unclean for some SPD matrix with that pattern.

An ordering is run through the elimination game and the Schur updates of Definition 2.6. It is
clean (Definition 2.24) if every position committed to L is nonzero, that is every pair {p, x}
with x a neighbour of the pivot p in the current game graph. Arithmetic is exact (fractions),
so every zero test is exact.

K3: the witness for the vertex a has unit diagonal, 1/2 on the two entries at a and 1/4 on the
opposite entry, so pivoting a first cancels the opposite pair: 1/4 - (1/2)(1/2) = 0.

E = {03, 04, 14, 23, 34}: the five witnesses of Remark 4.9. The witness for an ordering is
chosen by its first triangle vertex u and, for u = 3 (resp. 4), by whether the pendant 2
(resp. 1) precedes the earlier end of the pair that u zeroes. The script checks that this
choice defeats all 120 orderings, and that choosing by whether the pendant precedes u does not.
"""
import itertools
from fractions import Fraction as F

def pivots(A):
    """Pivots of Gaussian elimination in natural order, stopping at the first nonpositive one."""
    n = len(A)
    M = [row[:] for row in A]
    out = []
    for p in range(n):
        out.append(M[p][p])
        if M[p][p] <= 0:
            break
        for j in range(p + 1, n):
            f = M[j][p] / M[p][p]
            for k in range(p, n):
                M[j][k] -= f * M[p][k]
    return out

def is_spd(A):
    """Symmetric, and every pivot of Gaussian elimination in natural order is positive."""
    n = len(A)
    symmetric = all(A[i][j] == A[j][i] for i in range(n) for j in range(n))
    piv = pivots(A)
    return symmetric and len(piv) == n and all(x > 0 for x in piv)

def leading_minors(A):
    out, d = [], F(1)
    for x in pivots(A):
        d *= x
        out.append(d)
    return out

def pattern(A):
    n = len(A)
    return {frozenset((i, j)) for i in range(n) for j in range(i + 1, n) if A[i][j] != 0}

def pivot(M, p):
    """The pivot update of Definition 2.6 at p, on the survivors of the current matrix M."""
    rest = [v for v in M if v != p]
    return {j: {k: M[j][k] - M[j][p] * M[k][p] / M[p][p] for k in rest} for j in rest}

def schur(A, S):
    """The entries of A/A_S, by successive pivots (Lemma 2.4: the order within S is immaterial)."""
    M = {j: {k: F(A[j][k]) for k in range(len(A))} for j in range(len(A))}
    for p in S:
        M = pivot(M, p)
    return M

def committed_zeros(A, order):
    """The committed positions {p, x} that are zero when `order` is used (none iff clean)."""
    n = len(A)
    M = {j: {k: F(A[j][k]) for k in range(n)} for j in range(n)}
    adj = {v: {u for u in range(n) if u != v and A[u][v] != 0} for v in range(n)}
    zeros = []
    for p in order:
        zeros += [(p, x) for x in sorted(adj[p]) if M[p][x] == 0]
        for a, b in itertools.combinations(adj[p], 2):    # complete the neighbourhood of p
            adj[a].add(b)
            adj[b].add(a)
        for v in adj[p]:
            adj[v].discard(p)
        del adj[p]
        M = pivot(M, p)
    return zeros

# --- The triangle K3 ---
h, q = F(1, 2), F(1, 4)
K3 = {frozenset(e) for e in itertools.combinations(range(3), 2)}
T = {a: [[F(1) if i == j else (h if a in (i, j) else q) for j in range(3)] for i in range(3)]
     for a in range(3)}
for a, A in T.items():
    b, c = [v for v in range(3) if v != a]
    assert is_spd(A) and pattern(A) == K3
    abc = [[A[i][j] for j in (a, b, c)] for i in (a, b, c)]
    assert leading_minors(abc) == [1, F(3, 4), F(9, 16)]
    assert schur(A, [a])[b][c] == 0
orders3 = list(itertools.permutations(range(3)))
defeated = sum(bool(committed_zeros(T[order[0]], order)) for order in orders3)
clean = [sum(not committed_zeros(A, order) for order in orders3) for A in T.values()]
print("K3: three SPD witnesses with pattern K3, leading minors 1, 3/4, 9/16 in the order a, b, c;")
print("    pivoting a first cancels the opposite pair")
print(f"K3: orderings unclean for the witness of their first vertex: {defeated} of 6 (expected 6)")
print(f"K3: clean orderings of each witness: {clean} (expected [4, 4, 4])")

# --- The one-triangle pattern E of Remark 4.9 ---
E = {frozenset(map(int, e)) for e in ["03", "04", "14", "23", "34"]}
t = F(1, 3)
A0 = [[3, 0, 0, 1, 1], [0, 3, 0, 0, 1], [0, 0, 3, 1, 0], [1, 0, 1, 3, t], [1, 1, 0, t, 3]]
A3 = [[3, 0, 0, 1, h], [0, 3, 0, 0, 1], [0, 0, 3, 1, 0], [1, 0, 1, 2, 1], [h, 1, 0, 1, 3]]
A4 = [[3, 0, 0, h, 1], [0, 3, 0, 0, 1], [0, 0, 3, 1, 0], [h, 0, 1, 3, 1], [1, 1, 0, 1, 2]]
A3p = [row[:] for row in A3]
A3p[3][3] = F(7, 3)
A4p = [row[:] for row in A4]
A4p[4][4] = F(7, 3)
W = {name: [[F(x) for x in row] for row in A]
     for name, A in {"A(0)": A0, "A(3)": A3, "A(3)'": A3p, "A(4)": A4, "A(4)'": A4p}.items()}
MINORS = {"A(0)": [3, 9, 27, 63, 147], "A(3)": [3, 9, 27, 36, F(297, 4)],
          "A(3)'": [3, 9, 27, 45, F(195, 2)], "A(4)": [3, 9, 27, F(279, 4), F(297, 4)],
          "A(4)'": [3, 9, 27, F(279, 4), F(195, 2)]}
for name, A in W.items():
    assert is_spd(A) and pattern(A) == E and leading_minors(A) == MINORS[name], name
assert schur(W["A(0)"], [0])[3][4] == 0 and schur(W["A(3)"], [3])[0][4] == 0
assert schur(W["A(4)"], [4])[0][3] == 0
assert schur(W["A(3)'"], [2, 3])[0][4] == 0 and schur(W["A(4)'"], [1, 4])[0][3] == 0
print("E: five SPD witnesses with pattern E and the leading minors of Remark 4.9")

def witness(order, by_pair):
    """Remark 4.9's choice of witness. by_pair: compare the pendant with the earlier end of
    the pair that u zeroes (the corrected rule); otherwise compare it with u itself."""
    pos = {v: i for i, v in enumerate(order)}
    u = min((0, 3, 4), key=pos.get)
    if u == 0:
        return "A(0)"
    pendant, pair = (2, (0, 4)) if u == 3 else (1, (0, 3))
    first = min(pos[v] for v in pair) if by_pair else pos[u]
    return f"A({u})'" if pos[pendant] < first else f"A({u})"

orders = list(itertools.permutations(range(5)))
fixed = [o for o in orders if not committed_zeros(W[witness(o, True)], o)]
naive = [o for o in orders if not committed_zeros(W[witness(o, False)], o)]
print(f"E: orderings escaping the corrected choice of witness: {len(fixed)} of 120 (expected 0)")
print(f"E: orderings escaping the choice by 'pendant precedes u': {len(naive)} (expected 20)")
print("E: sigma = (3,2,0,1,4) with the displayed A(3): (A/A_3)_04 =", schur(W["A(3)"], [3])[0][4],
      "is refilled to (A/A_{2,3})_04 =", schur(W["A(3)"], [3, 2])[0][4],
      "| committed zeros:", committed_zeros(W["A(3)"], (3, 2, 0, 1, 4)))
