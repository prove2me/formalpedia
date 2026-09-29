-- Prove2me | Theorems.Thm_lean_workbook_plus_31325
-- name    : lean_workbook_plus_31325
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/67c63373-2b87-474b-ac15-6f81590b65af
-- statement:
--   since $ a^{2}+b^{2}+c^{2}\ge ab+bc+ca$ , we'll be done if we can show that\n $ a^{5}+b^{5}+c^{5}+abc(a^{2}+b^{2}+c^{2})\ge a^{4}b+ab^{4}+b^{4}c+bc^{4}+c^{4}a+ca^{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31325 : ∀ a b c : ℝ, a^5 + b^5 + c^5 + a * b * c * (a^2 + b^2 + c^2) ≥ a^4 * b + a * b^4 + b^4 * c + b * c^4 + c^4 * a + c * a^4   :=  by sorry
