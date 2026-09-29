-- Prove2me | Theorems.Thm_lean_workbook_plus_1536
-- name    : lean_workbook_plus_1536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/946b4029-7043-4087-96c7-b5aa0aefa52d
-- statement:
--   Solve the system of equation for $x_1,x_2,x_3,x_4\in \mathbb{R}$\n$$\begin{cases}x_1+x_2x_3x_4=2 \ x_2+x_3x_4x_1=2 \ x_3+x_4x_1x_2=2 \ x_4+x_1x_2x_3=2\end{cases}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1536 (x : ℕ → ℝ) : (∃ x_1 x_2 x_3 x_4 :ℝ, x_1 + x_2 * x_3 * x_4 = 2 ∧ x_2 + x_3 * x_4 * x_1 = 2 ∧ x_3 + x_4 * x_1 * x_2 = 2 ∧ x_4 + x_1 * x_2 * x_3 = 2) ↔ (∃ x_1 x_2 x_3 x_4 :ℝ, x_1 + x_2 * x_3 * x_4 = 2 ∧ x_2 + x_3 * x_4 * x_1 = 2 ∧ x_3 + x_4 * x_1 * x_2 = 2 ∧ x_4 + x_1 * x_2 * x_3 = 2)   :=  by sorry
