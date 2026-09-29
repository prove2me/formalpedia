-- Prove2me | Theorems.Thm_lean_workbook_plus_1849
-- name    : lean_workbook_plus_1849
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/db5e18e3-3075-481b-837c-f47ccd617d46
-- statement:
--   By AM-GM inequality, \(\frac{9}{13}a^4b+\frac{1}{13}b^4c+\frac{3}{13}c^4a\geq a^3bc\) and \(\frac{6}{13}a^4b+\frac{5}{13}b^4c+\frac{2}{13}c^4a\geq a^2b^2c\) and \(\frac{5}{13}a^4c+\frac{6}{13}b^4a+\frac{2}{13}c^4b\geq a^2b^2c\) and \(\frac{9}{13}a^4c+\frac{3}{13}b^4a+\frac{1}{13}c^4b\geq a^3bc\) and \(\frac{2}{7}a^3c^2+\frac{4}{7}b^3a^2+\frac{1}{7}c^3b^2\geq a^2b^2c\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1849 : ∀ a b c : ℝ, (9 / 13 * a ^ 4 * b + 1 / 13 * b ^ 4 * c + 3 / 13 * c ^ 4 * a ≥ a ^ 3 * b * c ∧ 6 / 13 * a ^ 4 * b + 5 / 13 * b ^ 4 * c + 2 / 13 * c ^ 4 * a ≥ a ^ 2 * b ^ 2 * c ∧ 5 / 13 * a ^ 4 * c + 6 / 13 * b ^ 4 * a + 2 / 13 * c ^ 4 * b ≥ a ^ 2 * b ^ 2 * c ∧ 9 / 13 * a ^ 4 * c + 3 / 13 * b ^ 4 * a + 1 / 13 * c ^ 4 * b ≥ a ^ 3 * b * c ∧ 2 / 7 * a ^ 3 * c ^ 2 + 4 / 7 * b ^ 3 * a ^ 2 + 1 / 7 * c ^ 3 * b ^ 2 ≥ a ^ 2 * b ^ 2 * c)   :=  by sorry
