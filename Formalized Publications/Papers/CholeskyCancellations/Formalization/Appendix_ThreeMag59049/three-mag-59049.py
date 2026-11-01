"""
three_mag_59049.py — 3^{10}=59049 three-magnitude colourings for n=5 unique-survivor
Tests Remark 5.7: minimum total survivors 8 and zero colourings with one survivor at every vertex.

We model t-values as magnitudes 0,1,2 representing alpha, beta, alpha+beta.
For each colouring of the 10 pairs (0..2), we compute for each apex u,
how many pairs (j,k) would be zeroed if apex had relation t_{jk}=t_{uj}+t_{uk}.
In magnitude model, this holds when mag[jk] == mag[uj]+mag[uk] (capped).
"""
import itertools

pairs = [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
pair_index = {p:i for i,p in enumerate(pairs)}

# Precompute for each apex u the list of pairs it could zero: pair (j,k) with u not in (j,k)
apex_to_pairs = {}
for u in range(5):
    lst=[]
    for (j,k) in pairs:
        if u not in (j,k):
            lst.append((j,k))
    apex_to_pairs[u]=lst

def survivors_for_colouring(mags):
    """mags list length 10 values 0,1,2. For each apex u, count survivors."""
    # For n=5, each apex has 3 other vertices besides itself? Actually W\{u} size 4, pairs among them C(4,2)=6 possible zeroed.
    # Survivor = vertex q that is never covered by zeroed pairs of u.
    total_survivors=0
    per_vertex_survivors={}
    all_one = True
    for u in range(5):
        covered=set()
        for (j,k) in apex_to_pairs[u]:
            # check if relation holds: mag[jk] == mag[uj]+mag[uk] ??? Use additive condition
            # Need mag indices
            def srt(a,b): return (a,b) if a<b else (b,a)
            idx_jk = pair_index[srt(j,k)]
            idx_uj = pair_index[srt(u,j)]
            idx_uk = pair_index[srt(u,k)]
            if mags[idx_jk] == mags[idx_uj] + mags[idx_uk]:
                covered.add(j); covered.add(k)
        # survivors are vertices in V\{u} not covered
        survivors = [v for v in range(5) if v!=u and v not in covered]
        per_vertex_survivors[u]=len(survivors)
        total_survivors+=len(survivors)
        if len(survivors)!=1:
            all_one=False
    return total_survivors, per_vertex_survivors, all_one

min_total=10
count_one_survivor=0
total=3**10
# Brute force 59049 feasible
for code in range(total):
    mags=[]
    tmp=code
    for _ in range(10):
        mags.append(tmp%3)
        tmp//=3
    # We restrict to 0,1,2 where 2 represents alpha+beta (1+1) etc. Allow 0 not allowed for t>0, but colouring includes 0 as small magnitude.
    # For strict positivity we require mag>=0, but we count.
    tot, per, all_one = survivors_for_colouring(mags)
    if tot < min_total:
        min_total=tot
    if all_one:
        count_one_survivor+=1

print(f"Enumerated {total} colourings")
print(f"Minimum total survivors: {min_total} (expected 8)")
print(f"Colourings with exactly one survivor at every vertex: {count_one_survivor} (expected 0)")
