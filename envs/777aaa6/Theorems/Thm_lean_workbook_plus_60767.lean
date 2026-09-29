-- Prove2me | Theorems.Thm_lean_workbook_plus_60767
-- name    : lean_workbook_plus_60767
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/05a8647e-14c3-4c33-8f7f-024227b0f883
-- statement:
--   Prove that $3x^2+y^2-xy \geq \left( y-\frac{1}{2}x \right)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60767 (x y : ℝ) : 3 * x ^ 2 + y ^ 2 - x * y ≥ (y - 1 / 2 * x) ^ 2 ∧ (y - 1 / 2 * x) ^ 2 ≥ 0   :=  by sorry
