-- Prove2me | Theorems.Thm_lean_workbook_plus_50720
-- name    : lean_workbook_plus_50720
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e6e2b7b3-a72a-4b1b-826e-b99f4e39032f
-- statement:
--   If $x<0$, prove that $\frac{x}{1+e^{-x}}<\frac{2}{7}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50720 (x : ℝ) (hx : x < 0) :
  x / (1 + exp (-x)) < 2 / 7   :=  by sorry
