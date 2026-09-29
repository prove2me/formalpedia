-- Prove2me | Theorems.Thm_lean_workbook_plus_22764
-- name    : lean_workbook_plus_22764
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1ec70b39-528f-4017-b5a5-97f0810c5f3b
-- statement:
--   Prove that $e^{-x} > -\frac{2x}{x^2 + 1}$ for $x \in \mathbb{R}^-$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22764 (x : ℝ) (hx : x < 0) :
  Real.exp (-x) > -2 * x / (x ^ 2 + 1)   :=  by sorry
