-- Prove2me | solution 1 for lean_workbook_plus_37716
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:13.774244+00:00
-- url     : https://prove2.me/submissions/b2fb2143-ba31-45c2-aa64-7cadb01b942b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (c : ℂ) (z : ℂ) : ‖c * z‖ = ‖c‖ * ‖z‖ := by
  norm_num
