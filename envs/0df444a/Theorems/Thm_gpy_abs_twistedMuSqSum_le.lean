-- Prove2me | Theorems.Thm_gpy_abs_twistedMuSqSum_le
-- name    : gpy_abs_twistedMuSqSum_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T00:24:05.950857+00:00
-- url     : https://prove2.me/theorems/4d19146e-3de9-4b6d-8b45-65469d43eedf
-- title:
--   Absolute bound for the twisted Mertens sum
-- statement:
--   For Q at least 2, any fixed pattern, any coprime class M, and any log-power m, the absolute value of the twisted Mertens sum — the Möbius- and twisted-weight-weighted sum of (log n)^m over n in [1, Q] coprime to M — is at most (log Q)^m times exp(2 (k+1)^2 (log Q + 2)). This is an unconditional absolute/tail bound for the twisted sums. It is NOT an asymptotic: it identifies no main term, and the asymptotic twisted Mertens bound remains open and is not claimed here. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_abs_twistedMuSqSum_le {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] (m M Q : ℕ) (hQ : 2 ≤ Q) :
    abs (∑ n ∈ (Finset.Icc 1 Q).filter (fun n : ℕ => Nat.Coprime n M), (ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ)) * (Real.log (n : ℝ)) ^ m) ≤ (Real.log (Q : ℝ)) ^ m * Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (Q : ℝ) + 2)) := by sorry
