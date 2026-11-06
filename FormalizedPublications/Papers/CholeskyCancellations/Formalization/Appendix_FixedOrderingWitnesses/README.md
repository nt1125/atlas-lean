# Appendix: source of fixed_ordering_witnesses.py.

This appendix contains fixed_ordering_witnesses.py, the script that checks the witnesses of Remark 4.9: no fixed ordering is clean for every SPD matrix with the pattern of a triangle, or with the one-triangle pattern E on five vertices. The triangle part is also formalized in Lean, in Section_4_PositiveResults/K_AdaptiveAndFixedOrderings.lean.

Reading order:

1. Papers/Script/fixed_ordering_witnesses.py — the fixed-ordering script: in exact arithmetic, the three SPD realizations of the triangle defeat all 6 orderings, and the five SPD realizations of E defeat all 120 orderings when the witness is chosen by whether the pendant precedes the earlier end of the zeroed pair; choosing by whether the pendant precedes the first triangle vertex leaves 20 orderings clean.
