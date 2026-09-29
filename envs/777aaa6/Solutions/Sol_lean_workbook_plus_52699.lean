-- Prove2me | solution 1 for lean_workbook_plus_52699
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:06.54915+00:00
-- url     : https://prove2.me/submissions/6bcf9ec2-2892-4a85-a384-9a50323ac01d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (1 - Real.sqrt 2) / (-1) = Real.sqrt 2 - 1 := by
  (intros; linarith)
