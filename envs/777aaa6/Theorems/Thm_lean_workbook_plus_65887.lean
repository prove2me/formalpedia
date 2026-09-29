-- Prove2me | Theorems.Thm_lean_workbook_plus_65887
-- name    : lean_workbook_plus_65887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0d40f074-91b5-4566-89d3-439371f0b5d0
-- statement:
--   Show that $\left( \frac{x+1}{2} \right)^2 \leq 1$ for $0 < x < 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65887 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  (x + 1) ^ 2 / 4 ≤ 1   :=  by sorry
