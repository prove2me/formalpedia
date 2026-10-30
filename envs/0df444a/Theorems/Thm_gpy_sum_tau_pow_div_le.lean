-- Prove2me | Theorems.Thm_gpy_sum_tau_pow_div_le
-- name    : gpy_sum_tau_pow_div_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:42:08.677643+00:00
-- url     : https://prove2.me/theorems/0b99d1c1-85cb-4b6d-9e72-c93015a1285d
-- title:
--   Reciprocal power moments of the 2-fold divisor count
-- statement:
--   For Q at least 1 and any r, the sum over d between 1 and Q of the r-th power of the 2-fold divisor count of d divided by d is at most (1 + log Q)^(2^r), by induction on r using submultiplicativity and the divisor reindexing; the recursion U_{r+1} at most U_r^2 is what produces the exponent 2^r. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_tau_pow_div_le (r : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ d ∈ Finset.Icc 1 Q, (((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d))).filter (fun t => ∏ i, t i = (d))).card : ℝ) ^ r / (d : ℝ)
      ≤ (1 + Real.log (Q : ℝ)) ^ (2 ^ r) := by sorry
