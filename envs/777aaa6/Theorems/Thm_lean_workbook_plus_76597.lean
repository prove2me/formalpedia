-- Prove2me | Theorems.Thm_lean_workbook_plus_76597
-- name    : lean_workbook_plus_76597
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/074fa98f-e663-46e6-9f98-83cb6e3e1448
-- statement:
--   Let $x, y$ be positive real numbers satisfying $x+y=1. $ Prove that $\frac{2}{x+3y}+\frac{1}{2x+y} \geq \frac{8}{5} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76597 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : 2 / (x + 3 * y) + 1 / (2 * x + y) ≥ 8 / 5   :=  by sorry
