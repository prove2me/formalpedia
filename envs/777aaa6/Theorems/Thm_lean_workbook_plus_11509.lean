-- Prove2me | Theorems.Thm_lean_workbook_plus_11509
-- name    : lean_workbook_plus_11509
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4dc38eb9-9cb2-40ee-80fc-407c7e8c35d7
-- statement:
--   Prove for every $x>0$ : $ln(x^3-2x^2+x+1)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11509 (x : ℝ) (hx: x > 0) : Real.log (x^3 - 2 * x^2 + x + 1) ≥ 0   :=  by sorry
