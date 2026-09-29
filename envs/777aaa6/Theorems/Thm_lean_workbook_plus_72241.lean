-- Prove2me | Theorems.Thm_lean_workbook_plus_72241
-- name    : lean_workbook_plus_72241
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2a808af6-e313-43a3-88aa-cf1dd1cb70b9
-- statement:
--   What is the sum of the first $100$ positive perfect cubes?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72241 (n : ℕ) : ∑ k in Finset.range 100, k^3 = 25502500   :=  by sorry
