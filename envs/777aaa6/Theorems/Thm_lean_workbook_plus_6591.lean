-- Prove2me | Theorems.Thm_lean_workbook_plus_6591
-- name    : lean_workbook_plus_6591
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/72b7c18b-e1c6-431c-b018-f80c301194f9
-- statement:
--   Given $f(x) = x + 1/(x+2)$, prove that $f(x) \geq 9/4$ for all $x \geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6591 (x : ℝ) (hx: x >= 2) : x + 1/(x+2) >= 9/4   :=  by sorry
