-- Prove2me | Theorems.Thm_lean_workbook_plus_40480
-- name    : lean_workbook_plus_40480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/03578b5c-6556-42cf-ba59-58a8941d5a78
-- statement:
--   Prove by contrapositive: if $a>b$ , then there is some natural $n$ for which $a>b+\frac1n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40480 (a b : ℝ) (h : a > b) : ∃ n : ℕ, a > b + 1 / n   :=  by sorry
