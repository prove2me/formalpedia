-- Prove2me | Theorems.Thm_gpy_sum_tupleProdCount_pow_four_range_le
-- name    : gpy_sum_tupleProdCount_pow_four_range_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:51:29.015201+00:00
-- url     : https://prove2.me/theorems/8b2ce1c8-bc4f-460f-8128-7667cd65c84d
-- title:
--   Fourth-order tau-moment bound, range form
-- statement:
--   For Q at least 1 and any k, the sum over L in range (Q+1) of the fourth power of the (k+1)-fold divisor count of L is at most Q times (1 + log Q)^(2^(4k) - 1), with constant 1 and the exponent carried exactly; the L = 0 term vanishes. This is the form used by divisor-weighted error sums. Like the interval form, it is one of two inputs for a divisor-weighted error estimate via Cauchy-Schwarz and does NOT by itself close that estimate, since a BDH-type second-moment bound on the errors is still missing and is not proved here. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_tupleProdCount_pow_four_range_le (k : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ L ∈ Finset.range (Q + 1), (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 4
      ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ (4 * k) - 1) := by sorry
