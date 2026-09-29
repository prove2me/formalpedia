-- Prove2me | Theorems.Thm_lean_workbook_plus_26426
-- name    : lean_workbook_plus_26426
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f1be69fe-9156-4e4c-a5b4-319330981de5
-- statement:
--   Let $a,b,c>0$ prove or disprove that:\n $ a^{4}+b^{4}+c^{4}+a^{2}b^{2}+a^{2}c^{2}+c^{2}b^{2}\geq a^{3}b+b^{3}c+c^{3}a+ab^{2}c+abc^{2}+a^{2}bc $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26426 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a^4 + b^4 + c^4 + a^2 * b^2 + a^2 * c^2 + b^2 * c^2 ≥ a^3 * b + b^3 * c + c^3 * a + a * b^2 * c + a * b * c^2 + a^2 * b * c   :=  by sorry
