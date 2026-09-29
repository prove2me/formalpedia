-- Prove2me | Theorems.Thm_lean_workbook_plus_63428
-- name    : lean_workbook_plus_63428
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/109cb5dc-5140-45da-aae2-0e6c9bf6c672
-- statement:
--   For injectivity: $\forall m,n\in\mathbb Z;\ r,s\in[0,a)$ such that $f_a(n,r)=f_a(m,s).$ i.e. $an+r=am+s,a(n-m)+r-s=0$ \nIf $n\ne m$ then $|a(n-m)|>|r-s|,$ but $|a(n-m)|=|r-s|,$ a contradiction, so $n=m,r=s.\ f_a$ is injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63428  (a : ℤ)
  (f : ℤ → ℕ → ℤ)
  (h₀ : ∀ n r, f n r = n * a + r)
  (h₁ : 0 < a) :
  Function.Injective f   :=  by sorry
