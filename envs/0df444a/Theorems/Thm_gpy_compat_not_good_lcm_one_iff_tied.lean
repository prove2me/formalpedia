-- Prove2me | Theorems.Thm_gpy_compat_not_good_lcm_one_iff_tied
-- name    : gpy_compat_not_good_lcm_one_iff_tied
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T01:07:23.230515+00:00
-- url     : https://prove2.me/theorems/ab13ea3b-5b0f-4141-af97-d3f774a5bbd0
-- title:
--   On the (1,1)-slice, defect equals the tied condition
-- statement:
--   On the slice where lcm(d_i, e_i) = 1, the defect condition is exactly the tied condition: some coordinate j different from i and prime p dividing lcm(d_j, e_j) with h_j = h_i or p dividing |h_i - h_j|. The prime is tied to its coordinate; a prime merely dividing the combined modulus and merely dividing some difference does not suffice, and that weaker statement is not claimed. Formalization Note: compatibility and goodness are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_compat_not_good_lcm_one_iff_tied {k : ℕ}
    {h d e : Fin k → ℕ} {i : Fin k} (hsqd : Squarefree (∏ j, d j))
    (hsqe : Squarefree (∏ j, e j)) :
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
      Nat.lcm (d i) (e i) = 1) ↔
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      Nat.lcm (d i) (e i) = 1 ∧
      ∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
        (h j = h i ∨
          p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) := by sorry
