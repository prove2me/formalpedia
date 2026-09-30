-- Prove2me | solution 1 for lean_workbook_plus_34190
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:53.656742+00:00
-- url     : https://prove2.me/submissions/a8809dc8-9d7c-4f9d-b9e2-25fa93b9912b

import Mathlib
set_option autoImplicit false

theorem solution  (x p : ℝ)
  (h₀ : 0 < x ∧ 0 < p)
  (h₁ : (1 + p / 100) * (1 - p / 100) * x = 1) :
  x = 10000 / (10000 - p^2)   := by
  have he : x * (10000 - p ^ 2) = 10000 := by nlinarith [h₁]
  have hd : 10000 - p ^ 2 ≠ 0 := by
    intro hz
    rw [hz] at he
    norm_num at he
  exact (eq_div_iff hd).2 he

#print axioms solution
