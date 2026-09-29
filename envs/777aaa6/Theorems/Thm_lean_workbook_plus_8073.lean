-- Prove2me | Theorems.Thm_lean_workbook_plus_8073
-- name    : lean_workbook_plus_8073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b743f486-b852-476e-9d2d-bf11874849a8
-- statement:
--   We only need to prove this when all of $x,y,z$ are negative (because other cases follow from this one) let $x=-a, y=-b, z=-c$ where $a,b,c$ are positive and $a^4+b^4+c^4=3$ . We need to prove $(a^3+b^3+c^3)+(a^2b+b^2c+c^2a)\le 6$ which is obviously true since \n$$a^3+b^3+c^3 \le 3\left(\frac {a^4+b^4+c^4}{3}\right)^{3/4} =3$$ and \n$$a^2b+b^2c+c^2a \le a^3+b^3+c^3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8073  (x y z : ℝ)
  (h₀ : x < 0 ∧ y < 0 ∧ z < 0)
  (h₁ : x^4 + y^4 + z^4 = 3) :
  x^3 + y^3 + z^3 + (x^2 * y + y^2 * z + z^2 * x) ≤ 6   :=  by sorry
