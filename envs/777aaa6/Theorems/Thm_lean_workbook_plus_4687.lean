-- Prove2me | Theorems.Thm_lean_workbook_plus_4687
-- name    : lean_workbook_plus_4687
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/dec17b0f-41c7-42bd-85e4-c61774f4b50b
-- statement:
--   prove that \n $ \boxed{\frac{a}{a^{2}+2bc}+\frac{b}{b^{2}+2ca}+\frac{c}{c^{2}+2ab}\leq\frac{a+b+c}{ab+bc+ca}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4687 : ∀ a b c : ℝ, (a / (a ^ 2 + 2 * b * c) + b / (b ^ 2 + 2 * c * a) + c / (c ^ 2 + 2 * a * b) ≤ (a + b + c) / (a * b + b * c + a * c))   :=  by sorry
