-- Prove2me | solution 1 for lean_workbook_plus_56296
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:40.054441+00:00
-- url     : https://prove2.me/submissions/d0916cca-6a4d-4104-ae1c-1be4c7318371

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ)
  (h₀ : 10 * s - s = 1 + s / 10) :
  s = 10 / 89 := by
  (intros; linarith)
