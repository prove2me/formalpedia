-- Prove2me | Theorems.Thm_lean_workbook_plus_19987
-- name    : lean_workbook_plus_19987
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d8026156-dfa4-45ca-9b38-23fa513f5e11
-- statement:
--   Solve in $R$ the system equation: $2^{\sin{x}}+\cos{y}=\frac{1}{2}$ , $2^{\sin{y}}+\cos{z}=\frac{1}{2}$ , $2^{\sin{z}}+\cos{x}=\frac{1}{2}$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19987 : ∀ x y z : ℝ, (2:ℝ)^Real.sin x + Real.cos y = 1 / 2 ∧ (2:ℝ)^Real.sin y + Real.cos z = 1 / 2 ∧ (2:ℝ)^Real.sin z + Real.cos x = 1 / 2 ↔ x = y ∧ y = z ∧ z = x   :=  by sorry
