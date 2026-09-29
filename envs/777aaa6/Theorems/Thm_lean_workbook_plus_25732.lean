-- Prove2me | Theorems.Thm_lean_workbook_plus_25732
-- name    : lean_workbook_plus_25732
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c8c09d3d-1bbd-49af-9e63-e68ba67c49df
-- statement:
--   Prove that the binomial theorem holds true. In other words, show that \((a + b)^n = \sum_{k=0}^n \binom{n}{k} a^{n - k} b^k\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25732 (a b : ℝ) (n : ℕ) : (a + b) ^ n = ∑ k in Finset.range (n + 1), (n.choose k) * a ^ (n - k) * b ^ k   :=  by sorry
