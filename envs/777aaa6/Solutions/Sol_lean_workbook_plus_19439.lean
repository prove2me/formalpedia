-- Prove2me | solution 1 for lean_workbook_plus_19439
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:18.285075+00:00
-- url     : https://prove2.me/submissions/0598f40c-da6d-4d93-a0ba-d83ff20a7695

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a^3 - b^3 = 25 * (a - b)) (h' : b^3 - c^3 = 49 * (b - c)) (h'' : c^3 - a^3 = 64 * (c - a)) : 8 * b + 5 * c = 13 * a := by
  (intros; linarith)
