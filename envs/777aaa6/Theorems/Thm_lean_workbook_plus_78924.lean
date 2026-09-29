-- Prove2me | Theorems.Thm_lean_workbook_plus_78924
-- name    : lean_workbook_plus_78924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/eada8df8-c73f-4a12-b8c8-4ba767feff7f
-- statement:
--   Then $x^2+y^2=33x+33y+2\cdot907=-33^2+2\cdot907,$ so $xy=\frac{\left(x+y\right)^2-\left(x^2+y^2\right)}{2}=\frac{33^2+33^2-2\cdot907}{2}=33^2-907=\boxed{182}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78924  (x y : ℤ)
  (h₀ : x + y = 33)
  (h₁ : x^2 + y^2 = 2 * 907 - 33^2) :
  x * y = 182   :=  by sorry
