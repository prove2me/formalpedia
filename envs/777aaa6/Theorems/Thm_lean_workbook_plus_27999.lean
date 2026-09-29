-- Prove2me | Theorems.Thm_lean_workbook_plus_27999
-- name    : lean_workbook_plus_27999
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2ce22e13-82d5-4524-9a65-b50955a1da13
-- statement:
--   Prove the inequality $\left(b^2c^2+c^2a^2+a^2b^2\right)\left(bc^2+cb^2+ca^2+ac^2+ab^2+ba^2\right) \geq 2abc\left(b^2c^2+c^2a^2+a^2b^2+bc\left(b^2+c^2\right)+ca\left(c^2+a^2\right)+ab\left(a^2+b^2\right)\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27999 ∀ a b c : ℝ, (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) * (b * c^2 + c * b^2 + c * a^2 + a * c^2 + b * a^2 + a * b^2) ≥ 2 * a * b * c * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2 + b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2))   :=  by sorry
