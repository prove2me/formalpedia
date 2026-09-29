-- Prove2me | solution 1 for lean_workbook_plus_55286
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:30.231003+00:00
-- url     : https://prove2.me/submissions/44eb0a32-266e-4850-9b9d-774515bd736f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 2 + 20 + 202 + 2022 = 2246) : 2 + 20 + 202 + 2022 = 2246 := by
  norm_num
