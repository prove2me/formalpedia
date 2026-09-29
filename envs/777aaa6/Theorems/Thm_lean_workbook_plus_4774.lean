-- Prove2me | Theorems.Thm_lean_workbook_plus_4774
-- name    : lean_workbook_plus_4774
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/26898daa-356f-4db4-a007-4d08442b8207
-- statement:
--   and from formula: $ \triangle=\frac{1}{2}\cdot bc \cdot \sin \alpha \implies 4\triangle =2bc\sin \alpha \implies 16 \triangle ^2=4b^2c^2 \cdot \sin^2 \alpha $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4774 : ∀ b c : ℝ, ∀ α : ℝ, (α ≠ 0 ∧ α ≠ π) → 16 * (1 / 2 * b * c * Real.sin α) ^ 2 = 4 * b ^ 2 * c ^ 2 * (Real.sin α) ^ 2   :=  by sorry
