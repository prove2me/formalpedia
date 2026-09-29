-- Prove2me | Theorems.Thm_lean_workbook_plus_14134
-- name    : lean_workbook_plus_14134
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/608ed898-6e62-4194-a0fe-759e250f8e78
-- statement:
--   $ \int x \sqrt {\frac {x - 1}{x + 1}}\,dx = \int \frac{x}{x + 1} \sqrt {x^2 - 1} dx$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14134 : ∀ x : ℝ, x * Real.sqrt ((x - 1) / (x + 1)) = (x / (x + 1)) * Real.sqrt (x ^ 2 - 1)   :=  by sorry
