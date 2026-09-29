-- Prove2me | Theorems.Thm_lean_workbook_plus_28378
-- name    : lean_workbook_plus_28378
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6c32a6e3-7300-4d85-a812-7086f263003f
-- statement:
--   $ 2e^{-a}(a+1)-e^{-a}(a+1)^{2}=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28378 : ∀ a : ℝ, (2 * (Real.exp (-a))) * (a + 1) - (Real.exp (-a)) * (a + 1) ^ 2 = 0   :=  by sorry
