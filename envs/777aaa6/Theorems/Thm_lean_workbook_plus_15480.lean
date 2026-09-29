-- Prove2me | Theorems.Thm_lean_workbook_plus_15480
-- name    : lean_workbook_plus_15480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/fe01c0ba-c9c0-47b8-a88c-dde955626226
-- statement:
--   Let $x,y \in \mathbb{R}^+_0$ , $x^2+y^2>2$ . Prove that $x^3+y^3>2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15480 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^2 + y^2 > 2) : x^3 + y^3 > 2   :=  by sorry
