-- Prove2me | Theorems.Thm_lean_workbook_plus_43787
-- name    : lean_workbook_plus_43787
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/97b106b1-0c46-40af-8924-e27cbf4f9dd7
-- statement:
--   $f(x+y)+f(x-y)=\frac{(x+y)^2}{2}+\frac{(x-y)^2}{2}=\frac{x^2+2xy+y^2}{2}+\frac{x^2-2xy+y^2}{2}=x^2+y^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43787  (x y : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 / 2)
  (h₁ : ∀ x, ∀ y, f (x + y) + f (x - y) = (x + y)^2 / 2 + (x - y)^2 / 2) :
  f (x + y) + f (x - y) = x^2 + y^2   :=  by sorry
