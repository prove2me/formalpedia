-- Prove2me | Theorems.Thm_lean_workbook_plus_3114
-- name    : lean_workbook_plus_3114
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/abf0e4d7-0e26-4983-983c-42526fb6da70
-- statement:
--   Graph the following\n$$f(x)=\begin{cases}\--2x+3 & \text{if}\ 0\leq{x}<5\\-3x+8 & \text{if}\ 5\leq{x}\leq{10}\end{cases}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3114 (f : ℝ → ℝ) (f_of : 0 ≤ x ∧ x < 5 → f x = -2 * x + 3) (f_on : 5 ≤ x ∧ x ≤ 10 → f x = -3 * x + 8) : 0 ≤ x ∧ x ≤ 10 → ∃ y, y = f x   :=  by sorry
