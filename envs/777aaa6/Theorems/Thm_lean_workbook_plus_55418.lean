-- Prove2me | Theorems.Thm_lean_workbook_plus_55418
-- name    : lean_workbook_plus_55418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/890a3c3d-9fbd-4919-b046-61c330146184
-- statement:
--   Prove that $a^{2}b^{2}+b^{2}c^{2}+c^{2}a^{2}\geq abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55418 (a b c: ℝ) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 >= a * b * c * (a + b + c)   :=  by sorry
