-- Prove2me | Theorems.Thm_lean_workbook_plus_8673
-- name    : lean_workbook_plus_8673
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/439e78d6-44b0-4943-9f9a-bf3093d93b73
-- statement:
--   Let $x$ and $y$ be two numbers satisfying the relations $x\ge 0$ , $y\ge 0$ , and $3x + 5y = 7$ . What is the maximum possible value of $9x^2 + 25y^2$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8673 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 3*x + 5*y = 7) : 9*x^2 + 25*y^2 ≤ 49   :=  by sorry
