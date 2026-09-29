-- Prove2me | Theorems.Thm_lean_workbook_plus_72909
-- name    : lean_workbook_plus_72909
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/818f66e9-907a-4ca0-b22b-db939b677c43
-- statement:
--   Prove that:\n$$1/2+1/2\,\sqrt {{\frac {ab+ca+bc}{{a}^{2}+{b}^{2}+{c}^{2}}}}\leq \sqrt {{\frac {{a}^{2}}{4\,{a}^{2}+5\,bc}}}+\sqrt {{\frac {{b}^{2}}{5\,ca+4\,{b}^{2}}}}+\sqrt {{\frac {{c}^{2}}{5\,ab+4\,{c}^{2}}}}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72909 : ∀ a b c : ℝ, 1 / 2 + 1 / 2 * Real.sqrt ((a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) ≤ Real.sqrt (a ^ 2 / (4 * a ^ 2 + 5 * b * c)) + Real.sqrt (b ^ 2 / (5 * c * a + 4 * b ^ 2)) + Real.sqrt (c ^ 2 / (5 * a * b + 4 * c ^ 2))   :=  by sorry
