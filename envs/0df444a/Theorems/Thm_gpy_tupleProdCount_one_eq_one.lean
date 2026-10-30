-- Prove2me | Theorems.Thm_gpy_tupleProdCount_one_eq_one
-- name    : gpy_tupleProdCount_one_eq_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:15:13.526373+00:00
-- url     : https://prove2.me/theorems/b1b73a4d-9441-47c1-8646-2384126e99ab
-- title:
--   The 1-fold divisor count of D is 1
-- statement:
--   For D at least 1, the number of ordered factorizations of D into a single positive factor is 1, since the only 1-tuple with product D is (D) itself. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_tupleProdCount_one_eq_one {D : ℕ} (hD : 1 ≤ D) :
    ((Fintype.piFinset (fun _ : Fin (1) => Finset.Icc 1 (D))).filter (fun t => ∏ i, t i = (D))).card = 1 := by sorry
