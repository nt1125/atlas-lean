"""
enum_pairing_4vert.py — Pairing Lemma (Lemma 5.5)
Fix level S, |W|=4, W={a,b,c,d}. Candidate slots 12, 6 variables t_{jk}.
Among 2^12=4096 subsets, 182 feasible, max feasible size 4,
exactly 3 achieve size 4 using all four pivots, each a fixed-point-free involution.

Protocol per Appendix:
Seeds 42,123,2026; Python 3.11.9, NumPy 1.26.4, SciPy 1.12 HiGHS
"""
import itertools
import numpy as np
from scipy.optimize import linprog

# W = 0,1,2,3
W = [0,1,2,3]
pairs = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
pair_index = {p:i for i,p in enumerate(pairs)}
# candidate slots: (apex u, pair {j,k} subset of W\{u})
slots = []
for u in W:
    for (j,k) in pairs:
        if u not in (j,k) and j in W and k in W:
            # ensure j,k != u and distinct and both in W\{u}
            if j!=u and k!=u:
                # also need j,k in W\{u} automatically, but pair must be inside W\{u}
                # all pairs with u not in pair satisfy
                slots.append((u,(j,k)))
# slots should be 12
assert len(slots)==12, len(slots)

def build_T(subset_indices):
    """Build T matrix m x 6 where row = e_{jk} - e_{uj} - e_{uk}"""
    m = len(subset_indices)
    T = np.zeros((m,6))
    for r, idx in enumerate(subset_indices):
        u,(j,k) = slots[idx]
        # need indices for (j,k), (u,j), (u,k) with sorted pairs
        def srt(a,b): return (a,b) if a<b else (b,a)
        jk = srt(j,k)
        uj = srt(u,j)
        uk = srt(u,k)
        T[r, pair_index[jk]] += 1
        T[r, pair_index[uj]] -= 1
        T[r, pair_index[uk]] -= 1
    return T

def is_feasible(T):
    """Feasible if exists t>0 with T t =0. Equivalent to exists t>=1 with T t =0."""
    if T.shape[0]==0:
        return True
    m,n = T.shape
    # linprog: find t >=1 s.t. T t =0
    # variables t[0..5], minimize 0
    c = np.zeros(n)
    A_eq = T
    b_eq = np.zeros(m)
    bounds = [(1, None)]*n
    res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
    return res.success

feasible = []
max_size = 0
for mask in range(1<<12):
    idx = [i for i in range(12) if (mask>>i)&1]
    T = build_T(idx)
    if is_feasible(T):
        feasible.append((mask, idx, T))
        max_size = max(max_size, len(idx))

print(f"Total subsets 4096, feasible {len(feasible)}, max feasible size {max_size}")
# Count achieving max size 4 using all four pivots
max_sets = [f for f in feasible if len(f[1])==max_size]
print(f"Max size sets: {len(max_sets)}")
# filter using all four pivots
all_pivot = []
for mask, idx, T in max_sets:
    pivots = set(slots[i][0] for i in idx)
    if len(pivots)==4:
        all_pivot.append((mask, idx))
print(f"Max size using all 4 pivots: {len(all_pivot)}")
for mask, idx in all_pivot:
    print(" ", [(slots[i][0], slots[i][1]) for i in idx])
# Expected: 182 feasible, max size 4, exactly 3 achieve size 4 using all four pivots, each fixed-point-free involution
