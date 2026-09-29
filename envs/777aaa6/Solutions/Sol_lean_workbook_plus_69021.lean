-- Prove2me | solution 1 for lean_workbook_plus_69021
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:18.927639+00:00
-- url     : https://prove2.me/submissions/30e5c495-c08f-44fd-b9d4-d556dfca420e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y u v : ℝ) (h : x * v = y * u) :
  x * (y + v) = y * (x + u) := by
  (intros; linarith)
