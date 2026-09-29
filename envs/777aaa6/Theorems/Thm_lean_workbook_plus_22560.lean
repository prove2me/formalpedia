-- Prove2me | Theorems.Thm_lean_workbook_plus_22560
-- name    : lean_workbook_plus_22560
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/af9db482-a2f4-489e-a3f3-0f3b90fc7350
-- statement:
--   prove: \n $ \frac{a^{2}}{b}+\frac{b^{2}}{c}+\frac{c^{2}}{a}\geq\frac{bc}{a}+\frac{ac}{b}+\frac{ab}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22560 : ∀ a b c : ℝ, (a^2 / b + b^2 / c + c^2 / a) ≥ (b * c / a + a * c / b + a * b / c)   :=  by sorry
