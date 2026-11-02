-- Prove2me | Theorems.Thm_gpy_defectCoeff_eq_parts_general
-- name    : gpy_defectCoeff_eq_parts_general
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T08:25:44.148638+00:00
-- url     : https://prove2.me/theorems/3525c62d-e4b8-4147-931f-b46cb5bc49ce
-- title:
--   The defect splits exactly into an i-part plus a tied sum, generally
-- statement:
--   The defect sum over general weights is exactly a compatible nontrivial-i-coordinate sum plus the tied difference/repeated sum, with no squarefree hypothesis. This is an unconditional exact decomposition; it does not bound the defect and does not claim smallness.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_defectCoeff_eq_parts_general {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1 then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) +
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
