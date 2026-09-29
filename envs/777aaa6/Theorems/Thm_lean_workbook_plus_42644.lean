-- Prove2me | Theorems.Thm_lean_workbook_plus_42644
-- name    : lean_workbook_plus_42644
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/baaa165b-6312-4e15-8255-79201ce1bd73
-- statement:
--   Try solving $x^4-x+1=(x^2+ax+b)(x^2-ax+c)$, this gives $b+c=a^2,ab-ac=1,bc=1$ Hence $b+{1\over b}=a^2,b-{1\over b}={1\over a}$ . Eliminating $b$ gives $4=(a^2+{1\over a})(a^2-{1\over a})=a^4-{1\over {a^2}}$ or $t^3-4t-1=0$ where $t:=a^2$ . This is solvable, now take for $a$ a solution of $a^2=t$ and you have factored $x^4-x+1$ as a product of two quadratics.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42644  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : b + c = a^2)
  (h₂ : a * b - a * c = 1)
  (h₃ : b * c = 1) :
  x^4 - x + 1 = (x^2 + a * x + b) * (x^2 - a * x + c)   :=  by sorry
