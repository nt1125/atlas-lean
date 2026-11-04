# Appendix: source of slot_counts.py.

This appendix contains slot_counts.py, the script that counts feasible slot families at four and five survivors and reruns the order-four slot search, in exact rational arithmetic with no linear-programming solver (Lemma 5.5, Remark 5.7, and the recomputation appendix). No Lean files.

Reading order:

1. slot_counts.py — the slot-count script: at four survivors, 182 of the 4096 slot sets are feasible, 15 have the maximum size 4, and 3 of those use all four apexes; on K4, 69075 of the 2^18 slot families are blocking and 633 are minimal; at five survivors, a feasible family has at most one slot per triple, the bound 10 is attained and realized, and none of the 288 configurations leaving one survivor at every apex is feasible.
