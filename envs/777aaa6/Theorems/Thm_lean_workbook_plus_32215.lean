-- Prove2me | Theorems.Thm_lean_workbook_plus_32215
-- name    : lean_workbook_plus_32215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/d633c43d-345a-4555-9d51-6b2e8a87bbca
-- statement:
--   So $x^3+1 = 2x\Rightarrow x^3-2x+1=0\Rightarrow (x-1)\cdot \left(x^2+x-1\right) = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32215  (x : ℝ)
  (h₀ : x^3 + 1 = 2 * x) :
  x^3 - 2 * x + 1 = 0   :=  by sorry
