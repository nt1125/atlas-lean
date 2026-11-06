# Appendix: source of enum-pairing-4vert.py.

The script for this appendix is `Papers/Script/enum-pairing-4vert.py`, which enumerates the candidate-slot subsets for the Pairing Lemma (Lemma 5.5) at a four-survivor level. All Python/GAP code is collected in `Papers/Script/`; this folder keeps only this guide. No Lean files.

Reading order:

1. Papers/Script/enum-pairing-4vert.py — the pairing-enumeration script: among the 2^12 = 4096 subsets, 182 are feasible and the maximum size is 4; 15 subsets have that size, and exactly 3 of them use all four pivots, each a fixed-point-free involution. It uses NumPy and SciPy; Papers/Script/slot_counts.py reproduces these counts in exact arithmetic with the standard library only.
