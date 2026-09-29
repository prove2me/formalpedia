-- Prove2me | Theorems.Thm_lean_workbook_plus_19176
-- name    : lean_workbook_plus_19176
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b44e9083-d084-419f-b369-b3ce6725523b
-- statement:
--   for the first one: $\frac{x^3}{x^2+y^2}\ge x-\frac{1}{2}y$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19176 : ∀ x y : ℝ, (x^3 / (x^2 + y^2) ≥ x - 1 / 2 * y)   :=  by sorry
