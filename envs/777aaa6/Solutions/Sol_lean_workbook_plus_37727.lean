-- Prove2me | solution 1 for lean_workbook_plus_37727
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:07.842641+00:00
-- url     : https://prove2.me/submissions/8d99ad2a-530a-4386-b3ca-001c38d2df8e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w z : ℂ) (h : z ≠ 0) : ‖w * z‖ = ‖w‖ * ‖z‖ := by
  norm_num
