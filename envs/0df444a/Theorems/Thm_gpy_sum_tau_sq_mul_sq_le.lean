-- Prove2me | Theorems.Thm_gpy_sum_tau_sq_mul_sq_le
-- name    : gpy_sum_tau_sq_mul_sq_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:53:35.059146+00:00
-- url     : https://prove2.me/theorems/ee9e89b2-1fc6-4f3f-97da-35d53fb857ca
-- title:
--   Cauchy-Schwarz bridge from the fourth tau-moment to divisor-weighted errors
-- statement:
--   For any real-valued error function e and any k and Q, the square of the sum over L in range (Q+1) of the square of the (k+1)-fold divisor count of L times e(L) is at most the product of the fourth-order tau-moment sum and the sum of e(L)^2. Combined with the fourth-order bound and a BDH-type bound on the sum of e(L)^2, this would yield a divisor-weighted error estimate; the BDH input is the remaining missing piece and is not proved here, so no such estimate is claimed. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_tau_sq_mul_sq_le (e : ℕ → ℝ) (k Q : ℕ) :
    (∑ L ∈ Finset.range (Q + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 2 * e L) ^ 2
      ≤ (∑ L ∈ Finset.range (Q + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 4)
        * (∑ L ∈ Finset.range (Q + 1), (e L) ^ 2) := by sorry
