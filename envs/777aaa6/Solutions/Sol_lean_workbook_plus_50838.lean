-- Prove2me | solution 1 for lean_workbook_plus_50838
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:45.571383+00:00
-- url     : https://prove2.me/submissions/21310b6a-9eeb-47d7-88a1-67ae804b514d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (a+b+c)^2 - (3/2)*(a*(b+c) + b*(c+a) + c*(a+b)) = (1/2)*((a-b)^2 + (b-c)^2 + (c-a)^2) := by
  (intros; linarith)
