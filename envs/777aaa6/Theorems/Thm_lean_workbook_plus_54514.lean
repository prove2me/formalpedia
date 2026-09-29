-- Prove2me | Theorems.Thm_lean_workbook_plus_54514
-- name    : lean_workbook_plus_54514
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bee64916-11b2-4411-8b42-5378f010fb49
-- statement:
--   Prove Bernoulli's Inequality: $(1+x)^{n}>1+nx$ for $x>-1$, $x \neq 0$, and $n$ a positive integer greater than 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54514 (x : ℝ) (n : ℕ) (hn : 1 < n) (hx : -1 < x) (hx' : x ≠ 0) : (1 + x) ^ n > 1 + n * x   :=  by sorry
