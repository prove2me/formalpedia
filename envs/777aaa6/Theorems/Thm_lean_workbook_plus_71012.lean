-- Prove2me | Theorems.Thm_lean_workbook_plus_71012
-- name    : lean_workbook_plus_71012
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b57d509d-b09b-458b-8c73-8fab78393d50
-- statement:
--   Prove that $\frac{x}{x^2+4} +\frac{3}{x+4}\leq \frac{4}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71012 : ∀ x : ℝ, (x / (x ^ 2 + 4) + 3 / (x + 4) ≤ 4 / 5)   :=  by sorry
