-- Prove2me | Theorems.Thm_lean_workbook_plus_22977
-- name    : lean_workbook_plus_22977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b088191f-48e1-4e1a-ba64-d4f17293305c
-- statement:
--   Write $n^2-19n+99=k^2$ for some integer $k$ . For all equations of this form, just complete the square: $(n-\frac{19}{2})^2+\frac{35}{4}=k^2$ . Now clear denominators and rearrange; we get $(2k)^2-(2n-19)^2=35$ . If it helps, let $x=2k$ even, $y=2n-19$ odd and solve $(x-y)(x+y)=35$ by equating factors of $35$ to $x-y$ , $x+y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22977  (n k : ℤ)
  (h₀ : n^2 - 19 * n + 99 = k^2) :
  (2 * k)^2 - (2 * n - 19)^2 = 35   :=  by sorry
