-- Prove2me | Theorems.Thm_lean_workbook_plus_65037
-- name    : lean_workbook_plus_65037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b38feb2a-0ffa-4787-a3e9-acc1adcc2e39
-- statement:
--   Let there be $x$ juniors and $y$ seniors in the after school program. Then, we know that $x+y=28$ . Also, from our conditions about how many are on the debate team, we get $0.25x=0.1y$ . We want to solve for $x$ , which is easy by multiplying the second equation by $10$ , substituting, and then getting that $x=\frac{28}{3.5}=\frac{2(28)}{7}=2(4)=8 \rightarrow \fbox{C}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65037  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : x + y = 28)
  (h₂ : 0.25 * x = 0.1 * y) :
  x = 8   :=  by sorry
