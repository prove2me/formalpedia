-- Prove2me | Theorems.Thm_lean_workbook_plus_1571
-- name    : lean_workbook_plus_1571
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0f5b5d9e-9779-4f70-bcbc-cdf84dafbe84
-- statement:
--   Show that for all constants a and b, and all real values of x, $ | a\ sin(x)+b\ cos(x) | \leq \sqrt{ a^{2}+b^{2}}$ . Is it possible to have equality? If so, for what value of x is the bound achieved?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1571 (a b x : ℝ) : |a * sin x + b * cos x| ≤ Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
