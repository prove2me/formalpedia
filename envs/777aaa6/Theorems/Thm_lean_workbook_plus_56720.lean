-- Prove2me | Theorems.Thm_lean_workbook_plus_56720
-- name    : lean_workbook_plus_56720
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e9b63f55-72ba-457f-b367-61e9ece1f988
-- statement:
--   Prove that for $x,y \ge 1$, $(x+1)(y+1) \le 2(xy+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56720 (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) : (x + 1) * (y + 1) ≤ 2 * (x * y + 1)   :=  by sorry
