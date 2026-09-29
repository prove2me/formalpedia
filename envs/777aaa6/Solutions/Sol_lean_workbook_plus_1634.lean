-- Prove2me | solution 1 for lean_workbook_plus_1634
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:32.42676+00:00
-- url     : https://prove2.me/submissions/e3d6544e-1bc7-415a-8e87-90254ba2f5b1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 117 + 11 + 2 = 130) : 117 + 11 + 2 = 130 := by
  norm_num
