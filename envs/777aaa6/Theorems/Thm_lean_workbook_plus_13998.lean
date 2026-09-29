-- Prove2me | Theorems.Thm_lean_workbook_plus_13998
-- name    : lean_workbook_plus_13998
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/048e712a-0792-4939-92cc-4f4c664c3b16
-- statement:
--   The following inequality is true: $\frac{1}{{{{\left( {a + 1} \right)}^2}}} + \frac{1}{{{{\left( {b + 1} \right)}^2}}} + \frac{1}{{{{\left( {c + 1} \right)}^2}}} + \frac{{a + b + c}}{4} \ge \frac{3}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13998 : ∀ a b c : ℝ, (a + 1) ^ (-2:ℤ) + (b + 1) ^ (-2:ℤ) + (c + 1) ^ (-2:ℤ) + (a + b + c) / 4 ≥ 3 / 2   :=  by sorry
