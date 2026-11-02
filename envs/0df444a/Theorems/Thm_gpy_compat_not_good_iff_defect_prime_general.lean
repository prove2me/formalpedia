-- Prove2me | Theorems.Thm_gpy_compat_not_good_iff_defect_prime_general
-- name    : gpy_compat_not_good_iff_defect_prime_general
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T06:48:54.443829+00:00
-- url     : https://prove2.me/theorems/7b7239fc-204e-4980-aeac-d8aeb7e37bad
-- title:
--   Compatible-and-not-good is exactly compatible-and-having-a-defect-prime, generally
-- statement:
--   For a support pair with nonzero coordinate lcms, being compatible and not good at coordinate i is equivalent to being compatible and having a defect prime. This holds with no squarefree hypothesis. This is an unconditional exact characterization; it does not bound the defect.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_compat_not_good_iff_defect_prime_general {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} (hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0) :
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
