-- Prove2me | Theorems.Thm_lean_workbook_plus_54149
-- name    : lean_workbook_plus_54149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8b815364-2eab-4bc9-a92f-2bee5f24baf5
-- statement:
--   Let the number be $x$. \n $\frac{x-9}{3}=43$ \n $x-9=129$ \n $x=138$ \nCorrect answer $=\frac{x-3}{9}$ \n $=\dfrac{138-3}{9}=15$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54149  (x : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : (x - 9) / 3 = 43) :
  (x - 3) / 9 = 15   :=  by sorry
