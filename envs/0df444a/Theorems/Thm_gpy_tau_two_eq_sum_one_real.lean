-- Prove2me | Theorems.Thm_gpy_tau_two_eq_sum_one_real
-- name    : gpy_tau_two_eq_sum_one_real
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:35:56.907401+00:00
-- url     : https://prove2.me/theorems/324fcdb6-b81f-4043-93a1-1faeb2ad7c2e
-- title:
--   The 2-fold divisor count as a real divisor sum
-- statement:
--   For d at least 1, the 2-fold divisor count of d, as a real number, equals the sum of 1 over the divisors of d. Formalization Note: the 2-fold divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_tau_two_eq_sum_one_real {d : ℕ} (hd : 1 ≤ d) :
    (((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d))).filter (fun t => ∏ i, t i = (d))).card : ℝ) = ∑ e ∈ Nat.divisors d, (1 : ℝ) := by sorry
