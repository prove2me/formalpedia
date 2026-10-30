-- Prove2me | Theorems.Thm_gpy_sum_tupleProdCount_pow_four_le
-- name    : gpy_sum_tupleProdCount_pow_four_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:48:22.580933+00:00
-- url     : https://prove2.me/theorems/ef372e08-6232-45b0-8437-839e8aa0e1ba
-- title:
--   Fourth-order tau-moment bound, interval form
-- statement:
--   For Q at least 1 and any k, the sum over L between 1 and Q of the fourth power of the (k+1)-fold divisor count of L is at most Q times (1 + log Q)^(2^(4k) - 1), with constant 1 and the exponent carried exactly. For the classical case k = 1 the exponent is 2^4 - 1 = 15. This bound is one of two inputs for a divisor-weighted error estimate via Cauchy-Schwarz; it does NOT by itself close that estimate, since a BDH-type second-moment bound on the errors is still missing and is not proved here. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_tupleProdCount_pow_four_le (k : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ L ∈ Finset.Icc 1 Q, (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card : ℝ) ^ 4
      ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ (4 * k) - 1) := by sorry
