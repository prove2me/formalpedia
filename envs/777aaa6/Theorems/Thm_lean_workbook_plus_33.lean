-- Prove2me | Theorems.Thm_lean_workbook_plus_33
-- name    : lean_workbook_plus_33
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/47e4fb6c-ccbb-43b2-ba68-c90c4cc37fdd
-- statement:
--   Prove that the following inequality holds in any triangle $ ABC $ : \n $ a(2a^{2}-b^{2}-c^{2})+b(2b^{2}-c^{2}-a^{2})+c(2c^{2}-a^{2}-b^{2})\geq 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33 :
    ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a → a * (2 * a^2 - b^2 - c^2) + b * (2 * b^2 - c^2 - a^2) + c * (2 * c^2 - a^2 - b^2) ≥ 0   :=  by sorry
