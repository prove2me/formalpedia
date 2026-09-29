-- Prove2me | solution 1 for lean_workbook_plus_71974
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:58.696074+00:00
-- url     : https://prove2.me/submissions/6312b81e-63eb-4b5b-8ea6-6c8dad16192e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 2 * Real.sqrt 2 ≤ x) :
  3 * x - 2 ≥ 6 * Real.sqrt 2 - 2 := by
  (intros; linarith)
