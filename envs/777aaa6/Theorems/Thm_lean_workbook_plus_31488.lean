-- Prove2me | Theorems.Thm_lean_workbook_plus_31488
-- name    : lean_workbook_plus_31488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f7e07931-f21e-4c8e-b266-0d3ab083c7d4
-- statement:
--   $\implies{3x^2-12x\leq{0}}$ $\implies{0\leq{x}\leq{4}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31488  (x : ℝ)
  (h₀ : 3 * x^2 - 12 * x ≤ 0) :
  0 ≤ x ∧ x ≤ 4   :=  by sorry
