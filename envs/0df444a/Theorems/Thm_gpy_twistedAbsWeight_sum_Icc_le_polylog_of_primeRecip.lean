-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_sum_Icc_le_polylog_of_primeRecip
-- name    : gpy_twistedAbsWeight_sum_Icc_le_polylog_of_primeRecip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T08:51:39.451743+00:00
-- url     : https://prove2.me/theorems/6f000b4c-a521-41e3-be9d-037026d2d1e7
-- title:
--   Conditional polylog bound for the twisted absolute range sum
-- statement:
--   CONDITIONAL on the explicit, unproved Mertens-second-theorem hypothesis that the sum of 1/p over primes p <= T is at most log log T + C: the twisted absolute range sum over n in [1, T] is at most exp (2 (k+1)^2 (log log T + C)), hence polylogarithmic in T rather than polynomial. The Mertens bound is a hypothesis of the theorem, not proved here. No defect smallness is claimed.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_sum_Icc_le_polylog_of_primeRecip {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {T : ℕ} (hT : 2 ≤ T) (C : ℝ)
    (hprime : ∑ p ∈ (Finset.range (T + 1)).filter (fun p : ℕ => p.Prime),
        1 / (p : ℝ) ≤ Real.log (Real.log (T : ℝ)) + C) :
    ∑ n ∈ Finset.Icc 1 T, abs ((ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ))) ≤ Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (Real.log (T : ℝ)) + C)) := by sorry
