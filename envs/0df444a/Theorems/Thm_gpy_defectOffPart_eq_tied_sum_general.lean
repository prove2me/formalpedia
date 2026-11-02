-- Prove2me | Theorems.Thm_gpy_defectOffPart_eq_tied_sum_general
-- name    : gpy_defectOffPart_eq_tied_sum_general
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T08:10:53.558388+00:00
-- url     : https://prove2.me/theorems/d267a40a-cd4e-4059-b74f-b91f58f5365b
-- title:
--   The defect off-part equals the tied sum, in full generality
-- statement:
--   The off-part of the defect sum (compatible, not-good pairs on the (1,1)-slice) is exactly the tied sum over the full support, with no squarefree restriction. This is an unconditional exact identity; it does not bound the defect and does not claim smallness.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_defectOffPart_eq_tied_sum_general {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1 then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) := by sorry
