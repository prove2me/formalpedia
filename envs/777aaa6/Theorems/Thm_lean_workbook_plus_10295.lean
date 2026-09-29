-- Prove2me | Theorems.Thm_lean_workbook_plus_10295
-- name    : lean_workbook_plus_10295
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/0460bf51-2b1a-45d0-af2b-e2c03a594c20
-- statement:
--   Prove that $\binom{n-1+k}{n-1} = \binom{n-1+k}{k}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10295 (n k : ℕ) : choose (n - 1 + k) (n - 1) = choose (n - 1 + k) k   :=  by sorry
