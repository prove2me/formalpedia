-- Prove2me | solution 1 for lean_workbook_plus_63317
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:20.463179+00:00
-- url     : https://prove2.me/submissions/9fafaceb-b3f1-40fd-af7f-31ee4ceed35b

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ)
    (h₀ : 0 < x)
    (h₁ : 900 / (x - 5) = 900 / x + 2.5) :
    x = 45 := by
  have hx : x ≠ 0 := h₀.ne'
  have hx5 : x - 5 ≠ 0 := by
    intro h
    have h5 : x = 5 := by linarith
    rw [h, div_zero, h5] at h₁
    norm_num at h₁
  field_simp at h₁
  have hq : (x - 45) * (x + 40) = 0 := by nlinarith [h₁]
  rcases mul_eq_zero.mp hq with h | h
  · linarith
  · linarith
