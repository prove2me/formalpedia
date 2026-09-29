-- Prove2me | Theorems.Thm_lean_workbook_plus_25163
-- name    : lean_workbook_plus_25163
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d64b8a14-1ccc-4f0c-8f0e-3cd0a902958d
-- statement:
--   Prove: \\(\\frac{1}{{1^2}} + \\frac{1}{{2^2}} + \\frac{1}{{3^2}} + .....\frac{1}{{100^2}} > 1.4\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25163 : (∑ k in Finset.range 101, (1:ℝ) / (k + 1) ^ 2) > 1.4   :=  by sorry
