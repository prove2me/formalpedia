-- Prove2me | Theorems.Thm_lean_workbook_plus_26143
-- name    : lean_workbook_plus_26143
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f9556124-3d2f-49af-90e4-7a2f38475712
-- statement:
--   Prove that $\frac{a}{2a+b+2c}+\frac{b}{2b+c+2a}+\frac{c}{2c+a+2b}\leq \frac{3}{5}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26143 : ∀ a b c : ℝ, (a / (2 * a + b + 2 * c) + b / (2 * b + c + 2 * a) + c / (2 * c + a + 2 * b) : ℝ) ≤ 3 / 5   :=  by sorry
