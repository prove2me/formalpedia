-- Prove2me | Theorems.Thm_lean_workbook_plus_65524
-- name    : lean_workbook_plus_65524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ed01ef31-8748-4a49-89bf-4f72eab04ef1
-- statement:
--   For $x,y \in R$ such that $\frac{x^2}{2} \le y \le -2x^2 + 3x$, prove that $x^2 + y^2 \le 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65524 (x y : ℝ) (h₁ : x ^ 2 / 2 ≤ y) (h₂ : y ≤ -2 * x ^ 2 + 3 * x) : x ^ 2 + y ^ 2 ≤ 2   :=  by sorry
