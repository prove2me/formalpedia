-- Prove2me | Theorems.Thm_lean_workbook_plus_75207
-- name    : lean_workbook_plus_75207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bc18cf08-6c93-4d6f-b4a2-c76b8844d15d
-- statement:
--   Let $x,y>0$ and $xy=\frac {x-y}{x+3y}.$ Prove that $y\leq\frac {1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75207 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x * y = (x - y) / (x + 3 * y)) : y ≤ 1 / 3   :=  by sorry
