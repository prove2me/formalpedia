-- Prove2me | Theorems.Thm_lean_workbook_plus_57637
-- name    : lean_workbook_plus_57637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/40152013-41fd-4f28-84ba-3a3d1ebc72ff
-- statement:
--   Prove the inequality for the real numbers $x_1, x_2, ..., x_n$. $|x_1 + x_2 +...+x_n| \leq |x_1|+|x_2|+...+|x_n|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57637 (n : ℕ) (x : Fin n → ℝ) : |∑ i, x i| ≤ ∑ i, |x i|   :=  by sorry
