-- Prove2me | Theorems.Thm_lean_workbook_plus_24739
-- name    : lean_workbook_plus_24739
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2de8c79b-c013-443f-b86c-87736190c495
-- statement:
--   For inverse variation, it is usually in the form of $y=\frac{k}{x}$ where $k$ is the constant of proportionality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24739 (x y : ℝ) (h₁ : x ≠ 0) (h₂ : y ≠ 0) (h₃ : x * y = k) : y = k / x   :=  by sorry
