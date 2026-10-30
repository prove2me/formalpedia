-- Prove2me | Theorems.Thm_gpy_sum_tau_div_le
-- name    : gpy_sum_tau_div_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:39:02.617802+00:00
-- url     : https://prove2.me/theorems/51f3cf67-4a60-4c7c-9bad-f1f35dec4aa7
-- title:
--   The reciprocal first moment of the 2-fold divisor count
-- statement:
--   For Q at least 1, the sum over d between 1 and Q of the 2-fold divisor count of d divided by d is at most (1 + log Q)^2, from the harmonic bound alone via the divisor reindexing. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_tau_div_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ d ∈ Finset.Icc 1 Q, (((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d))).filter (fun t => ∏ i, t i = (d))).card : ℝ) / (d : ℝ)
      ≤ (1 + Real.log (Q : ℝ)) ^ 2 := by sorry
