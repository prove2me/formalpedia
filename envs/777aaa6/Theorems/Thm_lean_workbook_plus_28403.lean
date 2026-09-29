-- Prove2me | Theorems.Thm_lean_workbook_plus_28403
-- name    : lean_workbook_plus_28403
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a0762fb5-870a-450f-aa27-07d535cadd06
-- statement:
--   Prove that:\n$$1/2\leq \sqrt {{\frac {{a}^{2}}{4\,{a}^{2}+5\,bc}}}+\sqrt {{\frac {{b}^{2}}{5\,ac+4\,{b}^{2}}}}+\sqrt {{\frac {{c}^{2}}{5\,ab+4\,{c}^{2}}}}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28403 : ∀ a b c : ℝ, 1 / 2 ≤ Real.sqrt (a^2 / (4 * a^2 + 5 * b * c)) + Real.sqrt (b^2 / (5 * a * c + 4 * b^2)) + Real.sqrt (c^2 / (5 * a * b + 4 * c^2))   :=  by sorry
