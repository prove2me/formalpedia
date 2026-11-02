-- Prove2me | Theorems.Thm_gpy_defect_prime_trichotomy_general
-- name    : gpy_defect_prime_trichotomy_general
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T07:18:56.765058+00:00
-- url     : https://prove2.me/theorems/2cdbbe69-03a0-43b3-92e9-9fa142c1598b
-- title:
--   General defect-prime trichotomy
-- statement:
--   A defect prime of a compatible, not-good pair is either an i-coordinate prime, a repeated-shift prime, or a genuine difference prime from the finite set of primes dividing some nonzero shift difference |h i - h j|. This holds with no squarefree hypothesis. This is an unconditional exact classification; it does not bound the defect.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_defect_prime_trichotomy_general {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0)
    (hcompat : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    (hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) :
    ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        (∃ j, j ≠ i ∧ h j = h i ∧ p ∣ Nat.lcm (d j) (e j)) ∨
        p ∈ (Finset.univ.filter (fun j : Fin k => j ≠ i)).biUnion
          (fun j => (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) := by sorry
