-- Prove2me | Theorems.Thm_lean_workbook_plus_1783
-- name    : lean_workbook_plus_1783
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cb979f69-6505-4869-8322-3da4bf5b414b
-- statement:
--   Let the starting amount of apples be $a.$ Setting up an equation, there are $a-1$ apples left after Bob takes $1,$ $\left(1-\dfrac14\right)(a-1)=\dfrac34(a-1)$ apples left after Mary takes $\dfrac14$ of the apples, and $\left(\dfrac56\right)\left(\dfrac34\right)(a-1)+1=6$ apples left after Joe takes $\dfrac16$ of the apples and puts one back. Solving the equation for $a$ gives $\left(\dfrac56\right)\left(\dfrac34\right)(a-1)+1= \dfrac{5(a-1)}{8}+1=6 \implies \dfrac{5(a-1)}{8}=5 \implies 5(a-1)=40 \implies a-1 = 8,$ so $a = \boxed{9}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1783  (a : ℕ)
  (h₀ : 0 < a)
  (h₁ : a - 1 = 8) :
  a = 9   :=  by sorry
