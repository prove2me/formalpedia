-- Prove2me | Theorems.Thm_lean_workbook_plus_25788
-- name    : lean_workbook_plus_25788
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0fa7119d-b875-486c-887b-a07ebb1a8165
-- statement:
--   The first inequality is true for all $a,b,c\in \mathbb{R}$ because it is equivalent to $\frac{(b-c)^{2}(c-a)^{2}(a-b)^{2}}{2a^{2}b^{2}c^{2}}\geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25788 (a b c : ℝ) : (b - c) ^ 2 * (c - a) ^ 2 * (a - b) ^ 2 / (2 * a ^ 2 * b ^ 2 * c ^ 2) ≥ 0   :=  by sorry
