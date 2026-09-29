-- Prove2me | Theorems.Thm_lean_workbook_plus_55600
-- name    : lean_workbook_plus_55600
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d36547f5-af1e-476d-a149-05b90cfa37d5
-- statement:
--   For a positive integer $n$ and positive real number $x$, prove that there is a unique positive integer $s$ such that $\frac{1}{2^{s+1}} \le [nx]< \frac{1}{2^s}$ where $[m]$ denotes the fractional part of $m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55600 (n : ℕ) (x : ℝ) (hx : 0 < x) : ∃! s : ℕ, (1 / (2 ^ (s + 1))) ≤ (↑n * x) % 1 ∧ (↑n * x) % 1 < 1 / (2 ^ s)   :=  by sorry
