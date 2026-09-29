-- Prove2me | Theorems.Thm_lean_workbook_plus_49343
-- name    : lean_workbook_plus_49343
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6c65daba-99e4-4817-9b05-03637ebca2ce
-- statement:
--   The answer is Sum of $n*(2^{(100 - n)} - 1)$ where $n$ runs through 1 to 99.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49343 : ∑ k in Finset.Icc 1 99, (k * (2^(100 - k) - 1)) = 2^100 - 100   :=  by sorry
