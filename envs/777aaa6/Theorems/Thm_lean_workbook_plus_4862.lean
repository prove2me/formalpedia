-- Prove2me | Theorems.Thm_lean_workbook_plus_4862
-- name    : lean_workbook_plus_4862
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ad0d3745-34e0-4cbf-8289-100aa6744fa1
-- statement:
--   Prove the identity $\binom{n}{m} + \binom{n}{m+1} = \binom{n+1}{m+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4862 (n m : ℕ) : choose n m + choose n (m + 1) = choose (n + 1) (m + 1)   :=  by sorry
