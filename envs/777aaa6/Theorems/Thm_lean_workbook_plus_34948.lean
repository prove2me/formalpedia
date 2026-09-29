-- Prove2me | Theorems.Thm_lean_workbook_plus_34948
-- name    : lean_workbook_plus_34948
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/53bfe980-2043-48db-85e1-411e4b67945b
-- statement:
--   Say the probability the candidate wins district I is $x$ , the probability they win district II is $y$ , and the probability they win district III is $z$ . We have the three equations: \n\n $xz=0.55$ \n $(1-y)x=0.34$ \n $x(1-y)(1-z)=0.15$ \nDividing the third equation by the second equation, we get $1-z=\frac{15}{34}$ , so $z=\frac{19}{34}$ . Plugging that into the first equation, we get that $x=\frac{187}{190}$ . Finally, plugging that into the second equation we get $y=\frac{36}{55}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34948  (x y z : ℝ)
  (h₀ : x * z = 0.55)
  (h₁ : (1 - y) * x = 0.34)
  (h₂ : x * (1 - y) * (1 - z) = 0.15) :
  x = 187 / 190 ∧ y = 36 / 55 ∧ z = 19 / 34   :=  by sorry
