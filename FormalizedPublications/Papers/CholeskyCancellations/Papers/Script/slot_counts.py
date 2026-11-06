"""
slot_counts.py — feasible slot families at four and five survivors, and the slot search on K4
Tests Lemma 5.5 and Appendix H (the counts at a four-vertex level and on K4) and Remark 5.7
(no scheme leaving one survivor at every vertex at order five).

A slot (u, {j, k}) at a level with survivor set W says that pivoting the apex u cancels the pair
{j, k}; with nonzero legs it imposes t_jk = t_uj + t_uk (Lemma 2.33) on the log-magnitudes of the
pairs inside W. A family is feasible if these relations have a solution with every t > 0
(Definition 2.29). This is decided exactly: t > 0 may be replaced by t >= 1, the system being
homogeneous; equations are substituted away, then Fourier-Motzkin runs in rational arithmetic.
"""
import itertools
from fractions import Fraction as F

def level(nv):
    """Slots and relation rows at a level with survivors 0..nv-1."""
    pairs = list(itertools.combinations(range(nv), 2))
    index = {p: i for i, p in enumerate(pairs)}
    slots = [(u, p) for u in range(nv) for p in pairs if u not in p]
    def row(slot):
        u, (j, k) = slot
        r = [0] * len(pairs)
        r[index[(j, k)]] += 1
        r[index[tuple(sorted((u, j)))]] -= 1
        r[index[tuple(sorted((u, k)))]] -= 1
        return r
    return pairs, slots, row

def feasible(rows, nvar):
    """Whether rows . t = 0 has a solution with every t_v >= 1."""
    ineq = [([F(int(i == v)) for i in range(nvar)], F(1)) for v in range(nvar)]   # a . t >= b
    eqs = [[F(x) for x in r] for r in rows]
    while eqs:
        e = eqs.pop()
        piv = next((i for i, x in enumerate(e) if x != 0), None)
        if piv is None:
            continue
        sub = lambda a: [ai - a[piv] / e[piv] * ei for ai, ei in zip(a, e)]
        eqs = [sub(r) for r in eqs]
        ineq = [(sub(a), b) for a, b in ineq]
    for v in range(nvar):
        pos = [(a, b) for a, b in ineq if a[v] > 0]
        neg = [(a, b) for a, b in ineq if a[v] < 0]
        new = [(a, b) for a, b in ineq if a[v] == 0]
        for (ap, bp), (an, bn) in itertools.product(pos, neg):
            cp, cn = ap[v], -an[v]
            new.append(([cn * x + cp * y for x, y in zip(ap, an)], cn * bp + cp * bn))
        ineq, seen = [], set()
        for a, b in new:
            if not any(a):
                if b > 0:
                    return False                      # 0 >= b > 0
                continue
            if (tuple(a), b) not in seen:
                seen.add((tuple(a), b))
                ineq.append((a, b))
    return True

# --- Four survivors (Lemma 5.5) ---
pairs, slots, row = level(4)
fam = [[slots[i] for i in range(12) if m >> i & 1] for m in range(1 << 12)]
feas = [f for f in fam if feasible([row(s) for s in f], 6)]
top = max(len(f) for f in feas)
maxi = [f for f in feas if len(f) == top]
allapex = [f for f in maxi if len({u for u, _ in f}) == 4]
def partner(f):
    """For a family with one slot per apex: u -> the vertex lying neither at u nor in its pair."""
    return {u: next(x for x in range(4) if x != u and x not in p) for u, p in f}
involution = all(pi[pi[u]] == u for pi in map(partner, allapex) for u in pi)
print(f"Four survivors: {len(feas)} of 4096 slot sets feasible (expected 182), maximum size {top} "
      f"(expected 4), {len(maxi)} of that size (expected 15), {len(allapex)} using all four apexes "
      f"(expected 3), each a fixed-point-free involution: {involution}")

# --- The order-four slot search on K4 (Appendix H) ---
V = range(4)
slots4 = [({a}, jk) for a in V for jk in itertools.combinations([x for x in V if x != a], 2)]
slots4 += [(set(S), tuple(x for x in V if x not in S)) for S in itertools.combinations(V, 2)]
def spoils(slot, order):
    """On K4 every pair is predicted nonzero: the slot spoils the ordering iff S is the set of
    predecessors of the earlier of j, k (Definition 2.29)."""
    S, (j, k) = slot
    return set(order[:min(order.index(j), order.index(k))]) == S
masks = [sum(1 << i for i, s in enumerate(slots4) if spoils(s, o))
         for o in itertools.permutations(V)]                  # the slots spoiling each ordering
blocking = {m for m in range(1 << len(slots4)) if all(m & sm for sm in masks)}
minimal = [m for m in blocking
           if not any(m & ~(1 << i) in blocking for i in range(len(slots4)) if m >> i & 1)]
print(f"K4 slot search over {len(slots4)} slots: {len(blocking)} blocking families "
      f"(expected 69075), {len(minimal)} minimal (expected 633)")

# --- Five survivors (Remark 5.7) ---
pairs, slots, row = level(5)
triple = lambda s: frozenset((s[0],) + s[1])
same_triple = [(s, t) for s, t in itertools.combinations(slots, 2) if triple(s) == triple(t)]
assert len(same_triple) == 30 and not any(feasible([row(s), row(t)], 10) for s, t in same_triple)
print("Five survivors: two slots on one triple are never feasible (30 cases), so at most 10 slots")
line = [(u, (j, k)) for (j, k) in pairs for u in range(5) if j < u < k]     # points 0..4 on a line
assert len(line) == 10 and feasible([row(s) for s in line], 10)
A = [[F(1, 2 ** abs(j - k)) for k in range(5)] for j in range(5)]           # A_jk = 2^-|j-k|
M = [r[:] for r in A]
for p in range(5):
    assert M[p][p] > 0                                                      # SPD: positive pivots
    for j in range(p + 1, 5):
        M[j] = [x - M[j][p] / M[p][p] * y for x, y in zip(M[j], M[p])]
assert all(x != 0 for r in A for x in r)                                    # complete pattern
assert all(A[j][k] - A[j][u] * A[u][k] / A[u][u] == 0 for u, (j, k) in line)
print("Five survivors: the 10 slots (u, {j,k}) with u between j and k on a line are feasible, and")
print("    realized by the SPD matrix 2^-|j-k| (complete pattern, all ten cancellations exact)")
# One survivor at the apex u: two of its pairs, covering exactly three of the other four vertices.
options = {}
for u in range(5):
    own = [jk for jk in pairs if u not in jk]
    options[u] = [((u, p), (u, r)) for p, r in itertools.combinations(own, 2)
                  if len(set(p) | set(r)) == 3]
assert all(len(o) == 12 for o in options.values())
schemes = [sum(c, ()) for c in itertools.product(*options.values())
           if len({triple(s) for s in sum(c, ())}) == 10]       # one slot on each of the 10 triples
nfeas = sum(feasible([row(s) for s in c], 10) for c in schemes)
print(f"Five survivors: {len(schemes)} configurations leave one survivor at every apex with one "
      f"slot per triple (expected 288); feasible: {nfeas} (expected 0)")
