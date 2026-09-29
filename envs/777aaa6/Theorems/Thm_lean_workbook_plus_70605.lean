-- Prove2me | Theorems.Thm_lean_workbook_plus_70605
-- name    : lean_workbook_plus_70605
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4ae613cc-2522-4310-82b4-a10aa4da01df
-- statement:
--   Calculate the value of $c$ where $c=\frac{e^2}{\sqrt{2 \pi}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70605 (c : ℝ) (h₁ : c = e^2 / Real.sqrt (2 * π)) : c = e^2 / Real.sqrt (2 * π)   :=  by sorry
