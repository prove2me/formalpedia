-- Prove2me | solution 1 for lean_workbook_plus_78668
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:02.909167+00:00
-- url     : https://prove2.me/submissions/5c226b82-bbb9-4f99-bce4-d70cf243ec7c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a / b = a * (1 / b) := by
  (intros; ring)
