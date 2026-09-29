-- Prove2me | Theorems.Thm_lean_workbook_plus_46579
-- name    : lean_workbook_plus_46579
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/50a7f54b-4bba-4132-8a50-58c6ab5af9d1
-- statement:
--   Easy to see that if $a,b,c>0$ and $ab+bc+ca=3$ then $a+b+c\ge 3$ . Also, we may assume WLOG that $c\le 1$ because $a,b,c>1$ would imply $ab+bc+ca>3$ . By C-S we have then $(a^2+1+3)(1+b^2+3)(c^2+4)-125\ge (a+b+3)^2(c^2+4)-125\ge (3-c+3)^2(c^2+4)-125=(c-1)^2(c^2+9+10(1-c))\ge 0$ as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46579  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b + b * c + c * a = 3) :
  3 ≤ a + b + c   :=  by sorry
