-- Prove2me | solution 1 for lean_workbook_plus_55691
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:29.486702+00:00
-- url     : https://prove2.me/submissions/590c52be-3e8e-482d-971d-38bc340c7f58

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℕ → ℕ)
  (h₀ : ∀ k, 0 < k → ∀ a, f (k * a) = k * f a)
  : f 1 = f 2008 / 2008 ∧ f 1 = f 2009 / 2009 := by
  have h8 := h₀ 2008 (by norm_num) 1
  have h9 := h₀ 2009 (by norm_num) 1
  simp only [mul_one] at h8 h9
  rw [h8, h9]
  simp
