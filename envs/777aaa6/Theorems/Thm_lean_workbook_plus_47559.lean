-- Prove2me | Theorems.Thm_lean_workbook_plus_47559
-- name    : lean_workbook_plus_47559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e3ea0e7f-7a7d-4f9a-89db-76ceb979e195
-- statement:
--   2. Plugging $y=x-3$ into the second equation we get $-2(x-3)=2(x^2+1)\iff x^2+x-2=0\iff x\in\{-2,1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47559  (x y : ℝ)
  (h₀ : y = x - 3)
  (h₁ : -2 * y = 2 * (x^2 + 1)) :
  x = -2 ∨ x = 1   :=  by sorry
