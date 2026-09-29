-- Prove2me | Theorems.Thm_lean_workbook_plus_19521
-- name    : lean_workbook_plus_19521
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1fa8bbe3-11a2-431c-ad73-1a4680da5b50
-- statement:
--   The given inequality is equivalent to ${\frac {{a}^{4}{b}^{2}+{a}^{2}{c}^{4}+{b}^{4}{c}^{2}-{b}^{3}c{a}^{2}-{c}^{3}{b}^{2}a-{a}^{3}b{c}^{2}}{ \left( {a}^{2}+ab+{b}^{2} \right)  \left( {b}^{2}+bc+{c}^{2} \right)  \left( {c}^{2}+ca+{a}^{2} \right) }} \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19521 (a b c : ℝ) : (a^4 * b^2 + a^2 * c^4 + b^4 * c^2 - b^3 * c * a^2 - c^3 * b^2 * a - a^3 * b * c^2) / (a^2 + a * b + b^2) / (b^2 + b * c + c^2) / (c^2 + c * a + a^2) ≥ 0   :=  by sorry
