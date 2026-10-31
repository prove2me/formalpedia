-- Prove2me | Theorems.Thm_gpy_defectCoeff_lamSelberg_eq_sq
-- name    : gpy_defectCoeff_lamSelberg_eq_sq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T04:22:14.387364+00:00
-- url     : https://prove2.me/theorems/6179478c-e363-41cc-bfca-493f4369f4f2
-- title:
--   For the Selberg weight, the defect equals its squarefree restriction
-- statement:
--   The Selberg weight vanishes off squarefree products (its Mobius factor kills them), so its full defect sum equals its squarefree-restricted defect sum: every non-squarefree term is zero. Exact identity. Formalization Note: the Selberg weight is written out as its Mobius-times-cutoff form, in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_defectCoeff_lamSelberg_eq_sq {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by sorry
