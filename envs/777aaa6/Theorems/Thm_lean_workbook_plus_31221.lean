-- Prove2me | Theorems.Thm_lean_workbook_plus_31221
-- name    : lean_workbook_plus_31221
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6b5f8e1a-b938-4a9f-9f59-7ddd880af55c
-- statement:
--   By average rate, we know that $\dfrac{2\times2x}{2+x}=3$ . Solving, we get $x=6$ , which is $B$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31221  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 2 * 2 * x / (2 + x) = 3) :
  x = 6   :=  by sorry
