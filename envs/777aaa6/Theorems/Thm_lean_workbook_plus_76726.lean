-- Prove2me | Theorems.Thm_lean_workbook_plus_76726
-- name    : lean_workbook_plus_76726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/85c46adb-32e5-406e-ba4f-3d0f71580cec
-- statement:
--   Solve the system of equation for $x_1,x_2,x_3,x_4\in \mathbb{C}$\n$$\begin{cases}x_1+x_2x_3x_4=2 \ x_2+x_3x_4x_1=2 \ x_3+x_4x_1x_2=2 \ x_4+x_1x_2x_3=2\end{cases}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76726 (x : ℕ → ℂ) : (∃ x1 x2 x3 x4 :ℂ, x1 + x2 * x3 * x4 = 2 ∧ x2 + x3 * x4 * x1 = 2 ∧ x3 + x4 * x1 * x2 = 2 ∧ x4 + x1 * x2 * x3 = 2) ↔ (∃ x1 x2 x3 x4 :ℂ, x1 + x2 * x3 * x4 = 2 ∧ x2 + x3 * x4 * x1 = 2 ∧ x3 + x4 * x1 * x2 = 2 ∧ x4 + x1 * x2 * x3 = 2)   :=  by sorry
