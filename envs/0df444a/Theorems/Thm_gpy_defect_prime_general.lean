-- Prove2me | Theorems.Thm_gpy_defect_prime_general
-- name    : gpy_defect_prime_general
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T06:15:29.733638+00:00
-- url     : https://prove2.me/theorems/2f58b7a1-0f20-4d41-9d72-274fc4df8b44
-- title:
--   General defect prime, with no squarefree hypothesis
-- statement:
--   A compatible but not-good support pair has a defect prime: a prime dividing the combined lcm, either dividing the i-coordinate lcm or dividing another coordinate's lcm with a congruent shift. This holds in full generality, with no squarefree hypothesis, via a general Chinese remainder witness. This is an unconditional exact statement; it does not bound the defect.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_defect_prime_general {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0)
    (hcompat : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    (hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) :
    ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        ∃ j, j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧ h i ≡ h j [MOD p]) := by sorry
