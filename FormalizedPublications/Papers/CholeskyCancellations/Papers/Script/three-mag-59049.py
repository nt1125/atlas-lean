"""
three-mag-59049.py — 3^{10}=59049 three-magnitude colourings for n=5 unique-survivor
Tests Remark 5.7: minimum total survivors 8 and zero colourings with one survivor at every vertex.

Each of the 10 pairs gets one of three magnitudes alpha, beta, alpha+beta (colours 0, 1, 2),
with alpha, beta > 0 generic, i.e. linearly independent over Q. A magnitude is stored as its
coefficient vector over (alpha, beta), so the relation t_{jk} = t_{uj} + t_{uk} of Lemma 2.33
holds exactly when the coefficient vectors add up: exact integer arithmetic, no floating
point, and every magnitude is positive. For each apex u we mark the pairs (j,k) whose
relation holds; a vertex survives u if it lies in no marked pair.
"""
import itertools

pairs = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
pair_index = {p:i for i,p in enumerate(pairs)}

# colour -> coefficients of the magnitude over (alpha, beta)
MAG = {0: (1, 0), 1: (0, 1), 2: (1, 1)}

def srt(a,b): return (a,b) if a<b else (b,a)

# For each apex u, the pairs it could zero: (j,k) with u not in (j,k)
apex_to_pairs = {u: [(j,k) for (j,k) in pairs if u not in (j,k)] for u in range(5)}

def survivors_for_colouring(colours):
    """colours: 10 values in {0,1,2}. For each apex u, count the survivors of u."""
    mags = [MAG[c] for c in colours]
    total_survivors=0
    per_vertex_survivors={}
    all_one = True
    for u in range(5):
        covered=set()
        for (j,k) in apex_to_pairs[u]:
            jk = mags[pair_index[(j,k)]]
            uj = mags[pair_index[srt(u,j)]]
            uk = mags[pair_index[srt(u,k)]]
            # additive relation t_jk = t_uj + t_uk, exact for generic alpha, beta
            if jk == (uj[0] + uk[0], uj[1] + uk[1]):
                covered.add(j); covered.add(k)
        # survivors are vertices in V\{u} not covered
        survivors = [v for v in range(5) if v!=u and v not in covered]
        per_vertex_survivors[u]=len(survivors)
        total_survivors+=len(survivors)
        if len(survivors)!=1:
            all_one=False
    return total_survivors, per_vertex_survivors, all_one

min_total=None
count_one_survivor=0
enumerated=0
for colours in itertools.product(range(3), repeat=10):
    enumerated+=1
    tot, per, all_one = survivors_for_colouring(colours)
    if min_total is None or tot < min_total:
        min_total=tot
    if all_one:
        count_one_survivor+=1

print(f"Enumerated {enumerated} colourings")
print(f"Minimum total survivors: {min_total} (expected 8)")
print(f"Colourings with exactly one survivor at every vertex: {count_one_survivor} (expected 0)")
