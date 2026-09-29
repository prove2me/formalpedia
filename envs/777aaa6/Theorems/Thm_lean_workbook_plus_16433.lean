-- Prove2me | Theorems.Thm_lean_workbook_plus_16433
-- name    : lean_workbook_plus_16433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/901b658d-af50-4a53-943b-f90e59ebb70a
-- statement:
--   Is the statement correct? In the range $2/3<x<1$, we always have $\frac{1-x}{1+3x}<\frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16433 (x : ℝ) (h₁ : (2:ℝ)/3 < x) (h₂ : x < 1) : (1 - x) / (1 + 3 * x) < 1 / 3   :=  by sorry
