-- Prove2me | Theorems.Thm_gpy_abs_twistedMuSqSum_le_polylog_of_primeRecip
-- name    : gpy_abs_twistedMuSqSum_le_polylog_of_primeRecip
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T09:28:20.53578+00:00
-- url     : https://prove2.me/theorems/def92e2a-3fbd-4d74-9b16-6ec189ba8422
-- title:
--   Conditional polylog bound for the twisted Mertens sum
-- statement:
--   CONDITIONAL on the explicit, unproved Mertens-second-theorem hypothesis that the sum of 1/p over primes p <= Q is at most log log Q + C: the absolute twisted Mertens sum is at most (log Q)^m times exp (2 (k+1)^2 (log log Q + C)), so the polynomial factor of the unconditional bound is gone. The Mertens bound is a hypothesis, not proved here. No defect smallness is claimed: a polylog absolute bound does not show the defect is o(1).
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_abs_twistedMuSqSum_le_polylog_of_primeRecip {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] (m M Q : ℕ) (hQ : 2 ≤ Q) (C : ℝ)
    (hprime : ∑ p ∈ (Finset.range (Q + 1)).filter (fun p : ℕ => p.Prime),
        1 / (p : ℝ) ≤ Real.log (Real.log (Q : ℝ)) + C) :
    abs (∑ n ∈ (Finset.Icc 1 Q).filter (fun n : ℕ => Nat.Coprime n M), (ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ)) * (Real.log (n : ℝ)) ^ m) ≤ (Real.log (Q : ℝ)) ^ m * Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (Real.log (Q : ℝ)) + C)) := by sorry
