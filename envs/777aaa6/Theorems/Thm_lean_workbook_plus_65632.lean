-- Prove2me | Theorems.Thm_lean_workbook_plus_65632
-- name    : lean_workbook_plus_65632
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ee22a04f-d199-41bf-91a8-aa5560942d98
-- statement:
--   Prove that $\frac{v}{1+e^{-v}}<0$ for all $v<0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65632 (v : ℝ) (h : v < 0) : v / (1 + exp (- v)) < 0   :=  by sorry
