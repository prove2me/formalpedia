-- Prove2me | Theorems.Thm_lean_workbook_plus_63395
-- name    : lean_workbook_plus_63395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f490c481-c389-48f7-8186-440debcbcaf1
-- statement:
--   Prove that if $xyz<0$, then $x^2+y^2+z^2\geq\sqrt{xyz(x+y+z)}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63395 (x y z : ℝ) (h : x * y * z < 0) :
  x^2 + y^2 + z^2 ≥ Real.sqrt (x * y * z * (x + y + z))   :=  by sorry
