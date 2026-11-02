-- Prove2me | Theorems.Thm_gpy_compat_not_good_lcm_one_iff_tied_general
-- name    : gpy_compat_not_good_lcm_one_iff_tied_general
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T07:43:47.121448+00:00
-- url     : https://prove2.me/theorems/9c9b7a9f-27bf-49ba-85db-be54498314da
-- title:
--   On the (1,1)-slice the defect condition is exactly the tied condition, generally
-- statement:
--   For a support pair with nonzero coordinate lcms, being compatible, not good, and having i-coordinate lcm equal to 1 is equivalent to being compatible with i-coordinate lcm 1 and having a tied prime: a prime dividing another coordinate's lcm whose shift equals h i or whose prime divides a nonzero shift difference. This holds with no squarefree hypothesis. This is an unconditional exact characterization; it does not bound the defect.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_compat_not_good_lcm_one_iff_tied_general {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} (hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0) :
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
