-- Prove2me | Theorems.Thm_lean_workbook_plus_82846
-- name    : lean_workbook_plus_82846
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.51614+00:00
-- url     : https://prove2.me/theorems/b070ec21-97be-40fa-874f-bcd9f4ae42bf
-- statement:
--   lower bound :\n\n $$\dfrac{a}{b+c} + \dfrac{b}{a+c} + \dfrac{c}{a+b} >= 1.5$$ solution\n\n $a=x+y,b=y+z,c=x+z $ \n\n $\sum{\frac{(x+y)^2}{2z(x+y)+(x+y)^2}} >= \sum{\frac{(2x+2y+2z)^2}{2\sum{x^2}+6\sum{ xy}}} >= 3/2 $ \n\nthe last step can be proved by $ xy+yz+xz <= x^2+y^2+z^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82846  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
  a / (b + c) + b / (a + c) + c / (a + b) ≥ 1.5   :=  by sorry
