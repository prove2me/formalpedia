-- Prove2me | solution 1 for lean_workbook_plus_81029
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:54.997743+00:00
-- url     : https://prove2.me/submissions/fc7f4f3e-0b83-4596-ad01-8c86e386f291

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p k : ℕ) : ∃ x : ℕ, p ^ k ∣ x ^ (p - 1) - 1 := by
  exact ⟨1, by simp⟩
