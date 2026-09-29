-- Prove2me | Theorems.Thm_lean_workbook_plus_43131
-- name    : lean_workbook_plus_43131
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/095f0222-dbbb-4387-9133-740fedb92a45
-- statement:
--   $(2x^2-2x^3)^2(5x-2)=((2x-1)(5x^3-x^2)-2x^2(1+x))^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43131 : ∀ x : ℝ, (2 * x ^ 2 - 2 * x ^ 3) ^ 2 * (5 * x - 2) = ((2 * x - 1) * (5 * x ^ 3 - x ^ 2) - 2 * x ^ 2 * (1 + x)) ^ 2   :=  by sorry
