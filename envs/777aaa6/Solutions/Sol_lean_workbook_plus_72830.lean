-- Prove2me | solution 1 for lean_workbook_plus_72830
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:22.912919+00:00
-- url     : https://prove2.me/submissions/b4ff826f-99da-49fa-b5f4-5cc9f4bdd547

import Mathlib
set_option autoImplicit false

theorem solution (m n p q r : ℝ) (h₀ : n ≠ 0 ∧ q ≠ 0 ∧ n + q ≠ 0)
    (h₁ : m / n = r) (h₂ : p / q = r) : (m + p) / (n + q) = r := by
  apply (div_eq_iff h₀.2.2).mpr
  have hm := (div_eq_iff h₀.1).mp h₁
  have hp := (div_eq_iff h₀.2.1).mp h₂
  nlinarith

#print axioms solution
