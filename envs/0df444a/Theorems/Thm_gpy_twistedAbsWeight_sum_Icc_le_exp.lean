-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_sum_Icc_le_exp
-- name    : gpy_twistedAbsWeight_sum_Icc_le_exp
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:48:02.000083+00:00
-- url     : https://prove2.me/theorems/777af4fe-9fef-456b-a82e-aa9725fd0150
-- title:
--   Range absolute bound for the twisted weight
-- statement:
--   For T at least 2, the sum of the absolute twisted weight over n in [1, T] is at most exp(2 (k+1)^2 (log T + 2)). The bound passes through the truncated Euler product, uses the uniform local-count bound c_p at most (k+1)^2 together with c_p/(p-1) at most 2(k+1)^2/p, and the elementary harmonic bound on the sum of reciprocals of primes up to T. This is an unconditional absolute/tail bound; it identifies no asymptotic main term and claims none. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_sum_Icc_le_exp {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {T : ℕ} (hT : 2 ≤ T) :
    ∑ n ∈ Finset.Icc 1 T, abs ((ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ))) ≤ Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (T : ℝ) + 2)) := by sorry
