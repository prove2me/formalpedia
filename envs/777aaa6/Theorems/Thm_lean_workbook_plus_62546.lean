-- Prove2me | Theorems.Thm_lean_workbook_plus_62546
-- name    : lean_workbook_plus_62546
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ed6be152-7edf-47dc-82bc-c30bea96748d
-- statement:
--   Prove that: \n $\frac{1}{1-cos(x_1)}+\frac{1}{1-cos(x_2)}+\frac{1}{1-cos(x_3)}\ge 2$ ; $ x_1,x_2,x_3\in[-2\pi,2\pi], x_1+x_2+x_3=0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62546 : ∀ x y z : ℝ, x + y + z = 0 ∧ -2 * π ≤ x ∧ x ≤ 2 * π ∧ -2 * π ≤ y ∧ y ≤ 2 * π ∧ -2 * π ≤ z ∧ z ≤ 2 * π → 1 / (1 - Real.cos x) + 1 / (1 - Real.cos y) + 1 / (1 - Real.cos z) ≥ 2   :=  by sorry
