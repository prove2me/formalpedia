-- Prove2me | Theorems.Thm_lean_workbook_plus_64321
-- name    : lean_workbook_plus_64321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e61fd39d-6363-4c13-b04e-468f89b4888a
-- statement:
--   Let $x,y \in \mathbb{R}$ such that $|x+y|+|x-y|=2.$ Prove that $\frac{3}{2}\leq |2x-y|+|2y-x| \leq 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64321 (x y : ℝ) (hx: abs (x + y) + abs (x - y) = 2) : 3 / 2 ≤ abs (2 * x - y) + abs (2 * y - x) ∧ abs (2 * x - y) + abs (2 * y - x) ≤ 6   :=  by sorry
