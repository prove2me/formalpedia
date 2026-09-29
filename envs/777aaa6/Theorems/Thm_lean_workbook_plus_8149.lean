-- Prove2me | Theorems.Thm_lean_workbook_plus_8149
-- name    : lean_workbook_plus_8149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ba8aa97b-967e-4339-8a00-27581de0ac80
-- statement:
--   b) $ \frac{n^n}{(2^n)^2}= \frac{n^n}{2^{2n}}= ( \frac{n}{4} )^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8149 (n : ℕ) : (n^n / (2^n)^2 : ℝ) = (n / 4)^n   :=  by sorry
