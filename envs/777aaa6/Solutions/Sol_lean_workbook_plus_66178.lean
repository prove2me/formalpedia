-- Prove2me | solution 1 for lean_workbook_plus_66178
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:08.482808+00:00
-- url     : https://prove2.me/submissions/28a13dfc-9862-48b1-81ad-3bc8a9acab53

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

lemma cubic_full_factorization (a b c α β x0 x : ℂ)
    (h1 : -a = x0 + 2 * α) (h2 : b = 2 * α * x0 + α ^ 2 + β ^ 2)
    (h3 : -c = (α ^ 2 + β ^ 2) * x0) :
    x ^ 3 + a * x ^ 2 + b * x + c =
      (x - x0) * (x - (α + β * Complex.I)) * (x - (α - β * Complex.I)) := by
  have ha : a = -(x0 + 2 * α) := by linear_combination -h1
  have hc : c = -((α ^ 2 + β ^ 2) * x0) := by linear_combination -h3
  rw [ha, h2, hc]
  linear_combination (x - x0) * β ^ 2 * Complex.I_sq

lemma cubic_root_classification (a b c α β x0 x : ℂ)
    (h1 : -a = x0 + 2 * α) (h2 : b = 2 * α * x0 + α ^ 2 + β ^ 2)
    (h3 : -c = (α ^ 2 + β ^ 2) * x0) :
    x ^ 3 + a * x ^ 2 + b * x + c = 0 ↔
      x = x0 ∨ x = α + β * Complex.I ∨ x = α - β * Complex.I := by
  rw [cubic_full_factorization a b c α β x0 x h1 h2 h3]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

theorem solution (a b c α β : ℂ) (x0 : ℂ)
    (h1 : -a = x0 + 2 * α) (h2 : b = 2 * α * x0 + α ^ 2 + β ^ 2)
    (h3 : -c = (α ^ 2 + β ^ 2) * x0) : x0 ^ 3 + a * x0 ^ 2 + b * x0 + c = 0 := by
  exact (cubic_root_classification a b c α β x0 x0 h1 h2 h3).2 (Or.inl rfl)

#print axioms solution
