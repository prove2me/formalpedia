-- Prove2me | solution 1 for lean_workbook_plus_78541
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:52.225721+00:00
-- url     : https://prove2.me/submissions/8cb609a1-03c2-4d95-b765-c67360ce6dd0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution {a b c : ℝ} : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
