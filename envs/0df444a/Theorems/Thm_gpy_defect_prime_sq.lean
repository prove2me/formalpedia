-- Prove2me | Theorems.Thm_gpy_defect_prime_sq
-- name    : gpy_defect_prime_sq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T23:49:36.672893+00:00
-- url     : https://prove2.me/theorems/8d5cb403-7979-4896-93b3-695bd4f52413
-- title:
--   A squarefree defect pair has a defect prime
-- statement:
--   For squarefree products, a compatible but not-good pair has a defect prime: some prime p dividing the combined modulus that either divides the i-coordinate modulus or divides another coordinate's modulus with h_i congruent to h_j modulo p. The proof uses the prime-by-prime factorization of goodness; global compatibility rules out the local-compatibility clause failing, so the local non-congruence clause must fail at some prime. Formalization Note: compatibility and goodness are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_defect_prime_sq {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hsqd : Squarefree (∏ j, d j)) (hsqe : Squarefree (∏ j, e j))
    (hcompat : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    (hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) :
    ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        ∃ j, j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧ h i ≡ h j [MOD p]) := by sorry
