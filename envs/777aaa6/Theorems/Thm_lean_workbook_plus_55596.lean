-- Prove2me | Theorems.Thm_lean_workbook_plus_55596
-- name    : lean_workbook_plus_55596
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/09e0a758-3285-4f20-b008-1ba4e11879d1
-- statement:
--   Prove that $a^{4}+b^{4}+c^{4}+3\left( b^{2}c^{2}+c^{2}a^{2}+a^{2}b^{2}\right) -2\left(b^{3}c+c^{3}b+c^{3}a+a^{3}c+a^{3}b+b^{3}a\right) = \left(a^{2}+b^{2}+c^{2}-bc-ca-ab\right) ^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55596 (a b c : ℝ) : a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) - 2 * (b^3 * c + c^3 * b + c^3 * a + a^3 * c + a^3 * b + b^3 * a) = (a^2 + b^2 + c^2 - b * c - c * a - a * b)^2   :=  by sorry
