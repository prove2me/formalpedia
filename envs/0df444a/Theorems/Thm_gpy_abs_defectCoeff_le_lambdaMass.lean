-- Prove2me | Theorems.Thm_gpy_abs_defectCoeff_le_lambdaMass
-- name    : gpy_abs_defectCoeff_le_lambdaMass
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T06:47:23.510129+00:00
-- url     : https://prove2.me/theorems/a6773c09-0a3c-40cb-91dc-7ec2c234e9cf
-- title:
--   Crude mass bound for the defect (not a smallness bound)
-- statement:
--   The absolute value of the defect sum is at most the squared l1 mass of the coefficients, using only 1/L at most 1. This is recorded as a crude mass bound only; it does NOT show the defect is small relative to any main term, and no smallness claim is made. Formalization Note: all sums and gates are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_abs_defectCoeff_le_lambdaMass {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    abs (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) ≤
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R), abs (lam d)) *
        (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R), abs (lam e)) := by sorry
