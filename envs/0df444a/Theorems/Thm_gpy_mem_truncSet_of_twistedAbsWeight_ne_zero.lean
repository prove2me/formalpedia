-- Prove2me | Theorems.Thm_gpy_mem_truncSet_of_twistedAbsWeight_ne_zero
-- name    : gpy_mem_truncSet_of_twistedAbsWeight_ne_zero
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:45:57.021675+00:00
-- url     : https://prove2.me/theorems/641d919d-3194-477f-87a4-0db09cfc2200
-- title:
--   Nonzero absolute twisted weight forces membership in the truncated set
-- statement:
--   If d lies in [1, T] and its absolute twisted weight is nonzero, then d lies in the truncated set over the primes up to T: nonzero Möbius weight forces d squarefree, so every prime factor of d is at most T and occurs with exponent at most 1, hence at most 2. This is an unconditional, elementary support statement; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_mem_truncSet_of_twistedAbsWeight_ne_zero {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {T : ℕ} {d : ℕ} (hdT : d ∈ Finset.Icc 1 T) (hw : abs ((ArithmeticFunction.moebius d : ℝ) * ((∏ p ∈ d.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient d : ℕ) : ℝ))) ≠ 0) :
    d ∈ (Finset.range (∏ p ∈ (Finset.range (T + 1)).filter (fun p => p.Prime), p ^ 2 + 1)).filter (fun d =>
    1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ (Finset.range (T + 1)).filter (fun p => p.Prime) ∧ d.factorization p ≤ 2) := by sorry
