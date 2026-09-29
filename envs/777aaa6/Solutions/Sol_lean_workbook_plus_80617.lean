-- Prove2me | solution 1 for lean_workbook_plus_80617
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:53.971+00:00
-- url     : https://prove2.me/submissions/0459e4df-9e00-44c8-81bf-1e05607d0355

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b : ℕ) (h₁ : a > 0 ∧ b > 0) : ∃ a b, a ^ 2 - b ^ 2 = a * b - 1 := by
  exact ⟨1, 1, by norm_num⟩
