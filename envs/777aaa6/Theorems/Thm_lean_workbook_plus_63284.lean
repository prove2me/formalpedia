-- Prove2me | Theorems.Thm_lean_workbook_plus_63284
-- name    : lean_workbook_plus_63284
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/324e4fb9-0c70-4599-a17f-288dceda7188
-- statement:
--   LHS $ = \frac{1}{2}\left[e^{x} \cdot \frac{1-e^{nx}}{1-e^{x}}+e^{-x} \cdot \frac{1-e^{-nx}}{1-e^{-x}}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63284 : ∀ x : ℝ, ∀ n : ℤ, (1/2)*((exp x * (1 - exp (n * x))/(1 - exp x) + exp (-x) * (1 - exp (-n * x))/(1 - exp (-x))))  = (exp ((n:ℝ) * x) - 1) / (exp x - 1)   :=  by sorry
