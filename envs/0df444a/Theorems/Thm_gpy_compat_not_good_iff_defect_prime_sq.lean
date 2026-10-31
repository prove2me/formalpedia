-- Prove2me | Theorems.Thm_gpy_compat_not_good_iff_defect_prime_sq
-- name    : gpy_compat_not_good_iff_defect_prime_sq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T00:04:46.665659+00:00
-- url     : https://prove2.me/theorems/cf8eeb0a-aeca-442c-a21a-f163316ffb08
-- title:
--   Compatible-and-not-good equals compatible-and-having-a-defect-prime
-- statement:
--   For squarefree products, the exact if-and-only-if: a pair is compatible and not good exactly when it is compatible and has a defect prime in the sense of the previous statement. Formalization Note: compatibility and goodness are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_compat_not_good_iff_defect_prime_sq {k : ℕ}
    {h d e : Fin k → ℕ} {i : Fin k} (hsqd : Squarefree (∏ j, d j))
    (hsqe : Squarefree (∏ j, e j)) :
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) ↔
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        ∃ j, j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧ h i ≡ h j [MOD p])) := by sorry
