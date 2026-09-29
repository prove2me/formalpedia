-- Prove2me | Theorems.Thm_lean_workbook_plus_57613
-- name    : lean_workbook_plus_57613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3493e8d6-ac52-471a-ad59-d7e5ad4b540f
-- statement:
--   Prove that for any three real (not necessarily positive) numbers a, b, c, $a^{4}+b^{4}+c^{4}+3\left( b^{2}c^{2}+c^{2}a^{2}+a^{2}b^{2}\right)\geq 2\left(b^{3}c+c^{3}b+c^{3}a+a^{3}c+a^{3}b+b^{3}a\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57613 (a b c : ℝ) : a^4 + b^4 + c^4 + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) ≥ 2 * (b^3 * c + c^3 * b + c^3 * a + a^3 * c + a^3 * b + b^3 * a)   :=  by sorry
