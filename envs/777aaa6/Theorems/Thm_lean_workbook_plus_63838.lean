-- Prove2me | Theorems.Thm_lean_workbook_plus_63838
-- name    : lean_workbook_plus_63838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/27a60a62-b56b-4422-a315-4ca2ff09d011
-- statement:
--   Prove $\frac{x^2}{x+3} \geq \frac32$ for all $x\geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63838 (x : ℝ) (hx: x ≥ 3) : (x^2 / (x + 3)) ≥ 3 / 2   :=  by sorry
