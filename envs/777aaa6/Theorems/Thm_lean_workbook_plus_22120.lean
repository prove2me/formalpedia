-- Prove2me | Theorems.Thm_lean_workbook_plus_22120
-- name    : lean_workbook_plus_22120
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/746745a3-b3f1-4774-b1b0-30fc28dfc396
-- statement:
--   Take $a = \cos \alpha + \textrm{i}\sin \alpha$ , $b = \cos \beta + \textrm{i}\sin \beta$ , $c = \cos \gamma + \textrm{i}\sin \gamma$ . Then $|a|=|b|=|c|=1$ and $a+b+c=0$ , which are forcing $a,b,c$ to be the affixes of the vertices of some equilateral triangle inscribed in the unit circle. Therefore $b=\omega a$ and $c=\omega^2 a$ , for $\omega$ being a primitive $3$ -root of unity, thus with $\omega^3=1$ , $\omega^2+\omega+1=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22120  (a b c : ℂ)
  (h₀ : ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖c‖ = 1)
  (h₁ : a + b + c = 0) :
  ∃ α β γ : ℝ, a = exp (α * I) ∧ b = exp (β * I) ∧ c = exp (γ * I)   :=  by sorry
