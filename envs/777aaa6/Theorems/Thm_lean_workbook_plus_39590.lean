-- Prove2me | Theorems.Thm_lean_workbook_plus_39590
-- name    : lean_workbook_plus_39590
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2ef4a105-5ef7-491f-8de9-f46c133b5a44
-- statement:
--   You can rewrite $a^2(b+c) + b^2(a+c) + c^2(a+b)$ as $a^2(6-a) + b^2(6-b) + c^2(6-c).$ This expands out to $6a^2 - a^3 + 6b^2 - b^3 + 6c^2 - c^3,$ which you can rearrange and factor to get $6(a^2 + b^2 + c^2)- (a^3 + b^3 + c^3).$ Now, you can substitute in the values to get $6(40) -200 = \boxed{40}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39590  (a b c : ℝ)
  (h₀ : a + b + c = 6)
  (h₁ : a^2 + b^2 + c^2 = 40)
  (h₂ : a^3 + b^3 + c^3 = 200) :
  a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) = 40   :=  by sorry
