-- Prove2me | Theorems.Thm_lean_workbook_plus_30747
-- name    : lean_workbook_plus_30747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7fd01841-53b3-4267-844e-0ff98b0a36b0
-- statement:
--   $a^{2}+b^{2}+c^{2}=ab+bc+ca$ yields $\left(a^{2}+b^{2}+c^{2}\right)-\left(ab+bc+ca\right)=0$ . But some algebra shows that $\left(c-a\right)^{3}-\left(a-b\right)^{3}=\left(\left(c-a\right)-\left(a-b\right)\right)\cdot\left(\left(a^{2}+b^{2}+c^{2}\right)-\left(ab+bc+ca\right)\right) =\left(\left(c-a\right)-\left(a-b\right)\right)\cdot 0=0$ , so that $\left(c-a\right)^{3}=\left(a-b\right)^{3}$ . Since $x^{3}=y^{3}\Rightarrow x=y$ , this yields $c-a=a-b$ , and similarly we find that $a-b=b-c$ . Thus, the trivial equation $\left(c-a\right)+\left(a-b\right)+\left(b-c\right)=0$ becomes $\left(a-b\right)+\left(a-b\right)+\left(a-b\right)=0$ , or, equivalently, $\left(1+1+1\right)\left(a-b\right)=0$ . Since $1+1+1$ is invertible, this yields $a-b=0$ , so that $a=b$ . Similarly, $b=c$ . Thus, $a=b=c$ , and we are done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30747  (a b c : ℝ)
  (h₀ : a^2 + b^2 + c^2 = a * b + b * c + c * a)
  (h₁ : (c - a)^3 - (a - b)^3 = 0) :
  a = b ∧ b = c   :=  by sorry
