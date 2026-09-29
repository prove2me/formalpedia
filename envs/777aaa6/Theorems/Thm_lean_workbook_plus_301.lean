-- Prove2me | Theorems.Thm_lean_workbook_plus_301
-- name    : lean_workbook_plus_301
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7bd10998-d28f-4004-8ad5-de501f0804ff
-- statement:
--   $$ \frac{a^2+5b^2}{c^2} \geq \frac{5}{24}(3\sqrt[3] 5-21\sqrt[3] {25}-1) $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_301 (a b c : ℝ) : (a^2 + 5 * b^2) / c^2 ≥ (5:ℝ) / 24 * (3 * (5:ℝ)^(1 / 3) - 21 * (25:ℝ)^(1 / 3) - 1)   :=  by sorry
