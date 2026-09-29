-- Prove2me | Theorems.Thm_lean_workbook_plus_44583
-- name    : lean_workbook_plus_44583
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/191bb447-3f01-4721-9006-541c8d9452e7
-- statement:
--   So in our case we just need to check for $y=x;~z=\frac x{x-2};~2<x\leq3$ and get \n\n $$(x-2)(x-3)^2\geq0,$$ true
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44583  (x y z : ℝ)
  (h₀ : 2 < x ∧ x ≤ 3)
  (h₁ : y = x)
  (h₂ : z = x / (x - 2)) :
  (x - 2) * (x - 3)^2 ≥ 0   :=  by sorry
