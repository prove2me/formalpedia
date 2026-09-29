-- Prove2me | Theorems.Thm_lean_workbook_plus_33907
-- name    : lean_workbook_plus_33907
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/372fa2ce-2e80-4569-a48c-5aa036323da7
-- statement:
--   $$=\frac{4}{3}+\frac{4c(2-c)(c-1)^2}{(c^2+2)\left((2-c)^2+2\right)}\ge\frac{4}{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33907 : ∀ c : ℝ, (4 / 3 + (4 * c * (2 - c) * (c - 1) ^ 2) / ((c ^ 2 + 2) * ((2 - c) ^ 2 + 2))) ≥ 4 / 3   :=  by sorry
