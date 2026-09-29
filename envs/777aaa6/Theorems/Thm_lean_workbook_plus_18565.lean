-- Prove2me | Theorems.Thm_lean_workbook_plus_18565
-- name    : lean_workbook_plus_18565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/00a0cf0f-3cdf-4f77-a523-5fd0a62e10c8
-- statement:
--   $5(z+\frac{1}{z})=26$ , so $5z+\frac{5}{z}=26$ , so $5z^2-26z+5=0$ so $(z-5)(5z-1) = 0$ or $z=\frac{1}{5}, 5$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18565  (z : ℂ)
  (h₀ : 5 * (z + 1 / z) = 26) :
  z = 1 / 5 ∨ z = 5   :=  by sorry
