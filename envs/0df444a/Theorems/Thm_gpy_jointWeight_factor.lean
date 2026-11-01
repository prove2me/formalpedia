-- Prove2me | Theorems.Thm_gpy_jointWeight_factor
-- name    : gpy_jointWeight_factor
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T03:13:31.957495+00:00
-- url     : https://prove2.me/theorems/4a194a67-0010-4cd6-94ea-ae29e1fd5ff8
-- title:
--   GCD factorization of the joint local weight
-- statement:
--   At squarefree D and E, the joint local weight (the product over primes dividing lcm D E of the local good-choice counts, divided by phi (lcm D E)) factors into a gcd part, a D-only part, and an E-only part, each a product over the corresponding prime divisors divided by the totient of that part. This is an unconditional algebraic factorization; it does not evaluate any sum.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_jointWeight_factor {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {D E : ℕ}
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    ((∏ p ∈ (Nat.lcm D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ))
      = ((∏ p ∈ (Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (D / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (E / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ)) := by sorry
