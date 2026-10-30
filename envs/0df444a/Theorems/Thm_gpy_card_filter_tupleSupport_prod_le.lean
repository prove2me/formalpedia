-- Prove2me | Theorems.Thm_gpy_card_filter_tupleSupport_prod_le
-- name    : gpy_card_filter_tupleSupport_prod_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:54.847687+00:00
-- url     : https://prove2.me/theorems/ff78f81b-b35a-4d78-aa08-f59061349032
-- title:
--   Support fiber over a product is bounded by the divisor count
-- statement:
--   The support tuples with a given product D number at most tau_k(D), the number of ordered factorizations of D into k positive factors: such a tuple has all entries between 1 and D, hence is a k-factorization of D.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_card_filter_tupleSupport_prod_le {k R D : ℕ} :
    (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter (fun d => ∏ i, d i = D)).card
      ≤ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D)).card := by sorry
