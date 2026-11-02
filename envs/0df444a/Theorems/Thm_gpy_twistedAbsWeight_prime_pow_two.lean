-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_prime_pow_two
-- name    : gpy_twistedAbsWeight_prime_pow_two
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:36:38.999266+00:00
-- url     : https://prove2.me/theorems/29a9c28e-83e4-44fe-bba5-4675e9b5f37e
-- title:
--   Absolute twisted weight at a prime square is zero
-- statement:
--   For a prime p, the absolute twisted weight at p squared is zero, because the Möbius function vanishes at non-squarefree numbers. This is an unconditional, elementary vanishing statement; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_prime_pow_two {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {p : ℕ} (hp : p.Prime) :
    abs ((ArithmeticFunction.moebius (p ^ 2) : ℝ) * ((∏ p ∈ (p ^ 2).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient (p ^ 2) : ℕ) : ℝ))) = 0 := by sorry
