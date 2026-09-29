-- Prove2me | Theorems.Thm_lean_workbook_plus_25155
-- name    : lean_workbook_plus_25155
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f429363a-c7a7-4096-94ee-bca8fac7d1e1
-- statement:
--   For any $ a$ , we have the solution $ x=27a^3+1,y=3a(27a^3+1)^{9a^3},z=(27a^3+1)^{9a^3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25155 (a : ℝ) : ∃ x y z : ℝ, x = 27 * a ^ 3 + 1 ∧ y = 3 * a * (27 * a ^ 3 + 1) ^ (9 * a ^ 3) ∧ z = (27 * a ^ 3 + 1) ^ (9 * a ^ 3)   :=  by sorry
