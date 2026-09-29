-- Prove2me | Theorems.Thm_lean_workbook_plus_61026
-- name    : lean_workbook_plus_61026
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/d88dd5d5-534f-4763-b518-c610267c0a8e
-- statement:
--   Prove for every $x>0$ : $ln(x^3-2x^2+x+1)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61026 (x : ℝ) (hx : 0 < x) : Real.log (x^3 - 2 * x^2 + x + 1) ≥ 0   :=  by sorry
