-- Prove2me | Theorems.Thm_lean_workbook_plus_14146
-- name    : lean_workbook_plus_14146
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/269c6c07-2270-4e57-a9f8-99c286421702
-- statement:
--   The following inequality is true: $\frac{1}{{{{\left( {a + 1} \right)}^2}}} + \frac{1}{{{{\left( {b + 1} \right)}^2}}} + \frac{1}{{{{\left( {c + 1} \right)}^2}}} + \frac{{ab + bc + ca}}{8} \ge \frac{9}{8}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14146 : ∀ a b c : ℝ, (1 / (a + 1) ^ 2 + 1 / (b + 1) ^ 2 + 1 / (c + 1) ^ 2 + (a * b + b * c + c * a) / 8) ≥ 9 / 8   :=  by sorry
