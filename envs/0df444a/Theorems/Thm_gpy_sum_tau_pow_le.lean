-- Prove2me | Theorems.Thm_gpy_sum_tau_pow_le
-- name    : gpy_sum_tau_pow_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:45:18.674961+00:00
-- url     : https://prove2.me/theorems/26b648fc-7829-4a91-8f27-99ca37c8b352
-- title:
--   Power moments of the 2-fold divisor count
-- statement:
--   For Q at least 1 and any r, the sum over d between 1 and Q of the r-th power of the 2-fold divisor count of d is at most Q times (1 + log Q)^(2^r - 1), by induction on r using the reciprocal power moments. For r = 4 the exponent is 2^4 - 1 = 15, the classical exponent for the fourth moment of the divisor function. Formalization Note: the divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_tau_pow_le (r : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ d ∈ Finset.Icc 1 Q, (((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d))).filter (fun t => ∏ i, t i = (d))).card : ℝ) ^ r
      ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 ^ r - 1) := by sorry
