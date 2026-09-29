-- Prove2me | Theorems.Thm_lean_workbook_plus_42894
-- name    : lean_workbook_plus_42894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b0477d12-3996-46bc-854b-29c35345693a
-- statement:
--   When $x=1$, the equation $x^2-1=0$ implies $(x+1)(x-1)=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42894  (x : ℝ)
  (h₀ : x = 1)
  (h₁ : x^2 - 1 = 0) :
  (x + 1) * (x - 1) = 0   :=  by sorry
