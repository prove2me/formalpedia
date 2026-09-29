-- Prove2me | Theorems.Thm_lean_workbook_plus_59249
-- name    : lean_workbook_plus_59249
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c612e006-7763-408c-a5d6-02ece453692c
-- statement:
--   $s\geq 2\,r+\sqrt {3\,{r}^{2}-3\,\sqrt {3}{R}^{2}-2\,Rr+8\,{R}^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59249 : ∀ (s : ℝ) (r : ℝ) (R : ℝ), s ≥ 2 * r + Real.sqrt (3 * r^2 - 3 * Real.sqrt 3 * R^2 - 2 * R * r + 8 * R^2)   :=  by sorry
