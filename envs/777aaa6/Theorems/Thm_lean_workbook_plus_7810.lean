-- Prove2me | Theorems.Thm_lean_workbook_plus_7810
-- name    : lean_workbook_plus_7810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d3d29b83-4ab1-4a85-9a02-16cdd5d9b7a9
-- statement:
--   If $a,b,c,d\in\mathbb{R}^+$ and $a+b+c+d=1$ , prove that $ab+bc+cd\le\frac{1}{4}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7810 (a b c d : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a + b + c + d = 1) :
  a * b + b * c + c * d ≤ 1 / 4   :=  by sorry
