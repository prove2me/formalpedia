-- Prove2me | Theorems.Thm_lean_workbook_plus_26682
-- name    : lean_workbook_plus_26682
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/396a3503-51e4-4d7d-8fd9-8218f3ac2892
-- statement:
--   $y=-3/2 \implies x=-2 \implies (-2,-3/2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26682 (x y : ℝ) (h₁ : y = -3 / 2) (h₂ : x = -2) : (x, y) = (-2, -3 / 2)   :=  by sorry
