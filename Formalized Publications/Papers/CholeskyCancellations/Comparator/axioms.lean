-- Axioms probe. One `#print axioms` per boxed theorem of the paper
-- HTML plus the headline audit-response theorems (conjecture
-- refutations, fill/factor bridges, infeasibility and converse
-- forms). `Comparator/comparator.py` (step 4c) parses this output, and
-- cholesky_cancellations_comparator.json's theorem_names must match
-- this list. Run it via `lake env lean Comparator/axioms.lean` once a
-- Lake project exists at this root.

import CholeskyCancellations

#print axioms CholeskyCancellations.astar_counts
#print axioms CholeskyCancellations.astar_irreducible
#print axioms CholeskyCancellations.astar_posDef
#print axioms CholeskyCancellations.cancellation_additive
#print axioms CholeskyCancellations.clean_of_order_le_four
#print axioms CholeskyCancellations.dense_safety
#print axioms CholeskyCancellations.exchange
#print axioms CholeskyCancellations.factorEntry_ne_zero_iff
#print axioms CholeskyCancellations.factorMatrix_diag
#print axioms CholeskyCancellations.factorMatrix_eq_zero_of_afterIn
#print axioms CholeskyCancellations.factorMatrix_mul_transpose
#print axioms CholeskyCancellations.factorPattern_adj_iff_factorEntry
#print axioms CholeskyCancellations.fillGraphGame_adj_iff
#print axioms CholeskyCancellations.fillGraphGame_eq_fillGraph
#print axioms CholeskyCancellations.fill_graph_conjecture_refuted
#print axioms CholeskyCancellations.fill_path
#print axioms CholeskyCancellations.fill_path_example
#print axioms CholeskyCancellations.first_schur_conjecture_refuted
#print axioms CholeskyCancellations.forest_clean
#print axioms CholeskyCancellations.four_cycle
#print axioms CholeskyCancellations.four_cycle_infeasible
#print axioms CholeskyCancellations.fresh_fill
#print axioms CholeskyCancellations.fresh_fill_closure
#print axioms CholeskyCancellations.general_cycle
#print axioms CholeskyCancellations.irreducible_iff_connected
#print axioms CholeskyCancellations.m2mMatrix_irreducible
#print axioms CholeskyCancellations.m2m_counterexample
#print axioms CholeskyCancellations.m2m_counterexample_all_orders
#print axioms CholeskyCancellations.m2m_curve_instance
#print axioms CholeskyCancellations.m2m_posDef
#print axioms CholeskyCancellations.magnitudes_converse
#print axioms CholeskyCancellations.magnitudes_forced
#print axioms CholeskyCancellations.max_edge
#print axioms CholeskyCancellations.monotone
#print axioms CholeskyCancellations.nesting
#print axioms CholeskyCancellations.pairing
#print axioms CholeskyCancellations.positives
#print axioms CholeskyCancellations.prefix_lemma
#print axioms CholeskyCancellations.refill
#print axioms CholeskyCancellations.schur_basic
#print axioms CholeskyCancellations.schur_quotient
#print axioms CholeskyCancellations.slot_empty_spoils_of_head
#print axioms CholeskyCancellations.spoils_example
#print axioms CholeskyCancellations.stiemke
#print axioms CholeskyCancellations.triangle
#print axioms CholeskyCancellations.triangle_necessary
#print axioms CholeskyCancellations.universal_pivot_refill
#print axioms CholeskyCancellations.universal_successor
#print axioms CholeskyCancellations.zero_leg
