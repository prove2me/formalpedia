-- Prove2me | solution 1 for lean_workbook_plus_34036
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:30.56996+00:00
-- url     : https://prove2.me/submissions/25c099a1-c793-48f1-982d-0cd0b10a06f0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ k ≥ 0, (k+2)^2+(k+3)^2+(k+5)^2+(k+8)^2=(k+1)^2+(k+4)^2+(k+6)^2+(k+7)^2 := by
  (intros; linarith)
