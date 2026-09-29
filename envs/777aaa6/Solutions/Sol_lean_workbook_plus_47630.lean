-- Prove2me | solution 1 for lean_workbook_plus_47630
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:18.206708+00:00
-- url     : https://prove2.me/submissions/b8cc0887-6a0b-4602-828e-52ab753043b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : a^2 * (b - c) + b^2 * (c - a) + c^2 * (a - b) = (a - b) * (a - c) * (b - c) := by
  (intros; linarith)
