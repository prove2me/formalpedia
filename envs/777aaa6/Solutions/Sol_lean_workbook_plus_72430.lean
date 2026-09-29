-- Prove2me | solution 1 for lean_workbook_plus_72430
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:13.663488+00:00
-- url     : https://prove2.me/submissions/60be83ce-45e0-4942-ad24-502ec4f6662f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x < 0) (h₂ : y - x < 1) : y < x + 1 := by
  (intros; linarith)
