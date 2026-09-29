-- Prove2me | solution 1 for lean_workbook_plus_46480
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:08.324567+00:00
-- url     : https://prove2.me/submissions/73d1db69-f6ba-4b6e-8c75-b49b95c49e64

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m t : ℝ)
  (h₀ : m + t = 12.48)
  (h₁ : m + 2 * t = 17.54) :
  m = 7.42 := by
  (intros; linarith)
