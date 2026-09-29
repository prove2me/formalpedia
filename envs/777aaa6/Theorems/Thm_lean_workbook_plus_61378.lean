-- Prove2me | Theorems.Thm_lean_workbook_plus_61378
-- name    : lean_workbook_plus_61378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4b2b9ea5-b424-4842-ab2f-80b76d29bc2e
-- statement:
--   Because $14 \\left[\\sum ab\\left(a^2+b^2 \\right) \\right] \ge 28\\sum a^2b^2$ and $9\\sum a^3b \ge 9abc \\left(a+b+c \\right),$ it's enough to prove $2\\sum a^4 + 7\\sum a^2b^2 \ge 9abc\\left(a+b+c \\right), \ \bf{(obvious)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61378 (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 7 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 9 * a * b * c * (a + b + c)   :=  by sorry
