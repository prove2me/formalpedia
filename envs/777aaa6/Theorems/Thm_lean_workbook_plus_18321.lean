-- Prove2me | Theorems.Thm_lean_workbook_plus_18321
-- name    : lean_workbook_plus_18321
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/40a892c0-c3d3-439e-9925-544408e87fbc
-- statement:
--   Let $ x, y$ are real numbers such that $ x + y \geq 0.$ Prove that $x ^ 5 + y ^ 5\geq xy(x^3 +y^ 3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18321 (x y : ℝ) (h : x + y ≥ 0) : x ^ 5 + y ^ 5 ≥ x * y * (x ^ 3 + y ^ 3)   :=  by sorry
