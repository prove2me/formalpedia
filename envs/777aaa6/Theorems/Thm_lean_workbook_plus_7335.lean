-- Prove2me | Theorems.Thm_lean_workbook_plus_7335
-- name    : lean_workbook_plus_7335
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7d807001-bac5-44e0-8242-053935916a36
-- statement:
--   Prove that $a^{4}+b^{4}+c^{4}+d^{4}+a^{3}b+b^{3}c+c^{3}d+d^{3}a \ge 2(ab^{3}+bc^{3}+cd^{3}+da^{3})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7335 ∀ a b c d: ℝ, a^4 + b^4 + c^4 + d^4 + a^3 * b + b^3 * c + c^3 * d + d^3 * a >= 2 * (a * b^3 + b * c^3 + c * d^3 + d * a^3)   :=  by sorry
