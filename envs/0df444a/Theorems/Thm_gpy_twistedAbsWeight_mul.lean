-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_mul
-- name    : gpy_twistedAbsWeight_mul
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:32:30.52467+00:00
-- url     : https://prove2.me/theorems/d52872cc-ca8b-4840-948c-960a01137a96
-- title:
--   Absolute twisted weight is multiplicative on coprime pairs
-- statement:
--   For coprime nonzero natural numbers m and n, the absolute twisted weight at m * n equals the product of the absolute twisted weights at m and at n. Both the Möbius function and the twisted weight are multiplicative on coprime pairs, and absolute value distributes over products. This is an unconditional, elementary multiplicativity statement; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_mul {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    abs ((ArithmeticFunction.moebius (m * n) : ℝ) * ((∏ p ∈ (m * n).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient (m * n) : ℕ) : ℝ))) = abs ((ArithmeticFunction.moebius m : ℝ) * ((∏ p ∈ m.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient m : ℕ) : ℝ))) * abs ((ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ))) := by sorry
