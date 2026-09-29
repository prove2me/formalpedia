-- Prove2me | Theorems.Thm_lean_workbook_plus_50702
-- name    : lean_workbook_plus_50702
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5b2ba4ca-fb32-4310-83f2-f0524f9ca671
-- statement:
--   The normal vector to the plane is $(4,-1,3)$ . Since the shortest distance is perpendicular to the plane, we know $(3,-1,2)+t \cdot (4,-1,3)$ is on the plane and we just need to solve for $t$ . We have $x_p=3+4t$ , $y_p=-1-t$ , and $z_p=2+3t$ . Plugging into the equation for the plane, we get $12+16t+1+t+6+9t+2=0$ . From this, we get that $t=\frac{-21}{26}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50702  (x y z : ℝ)
  (h₀ : x = 3 + 4 * t)
  (h₁ : y = -1 - t)
  (h₂ : z = 2 + 3 * t)
  (h₃ : 12 * x + 16 * y + 1 * z + 6 = 0) :
  t = -21 / 26   :=  by sorry
