-- Prove2me | Theorems.Thm_lean_workbook_plus_16324
-- name    : lean_workbook_plus_16324
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/eb1e415b-5faf-4a6b-a0ab-05e9dc122e21
-- statement:
--   Let $a\in\left[\frac 35,\frac 45\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16324 (a : ℝ) (h1 : 3 / 5 ≤ a) (h2 : a ≤ 4 / 5) : a ∈ Set.Icc (3 / 5) (4 / 5)   :=  by sorry
