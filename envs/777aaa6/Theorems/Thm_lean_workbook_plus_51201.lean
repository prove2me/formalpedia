-- Prove2me | Theorems.Thm_lean_workbook_plus_51201
-- name    : lean_workbook_plus_51201
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f834518b-1748-45cf-a1d4-efb9d15f9cd8
-- statement:
--   Prove that:\n$$1/2\leq \sqrt {{\frac {{a}^{2}}{4\,{a}^{2}+5\,bc}}}+\sqrt {{\frac {{b}^{2}}{5\,ac+4\,{b}^{2}}}}+\sqrt {{\frac {{c}^{2}}{5\,ab+4\,{c}^{2}}}}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51201 : ∀ a b c : ℝ, (1 / 2 : ℝ) ≤ Real.sqrt (a^2 / (4 * a^2 + 5 * b * c)) + Real.sqrt (b^2 / (5 * a * c + 4 * b^2)) + Real.sqrt (c^2 / (5 * a * b + 4 * c^2))   :=  by sorry
