-- Prove2me | solution 1 for lean_workbook_plus_64974
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:17:29.042165+00:00
-- url     : https://prove2.me/submissions/103a87dd-a09f-4d69-a99a-468250f9cd3f

import Mathlib

private theorem quadratic_pos (x : ℝ) : 0 < x^2 + x + 1 := by
  nlinarith only [sq_nonneg (x + (1/2 : ℝ))]

theorem bound_of_product_one (x y z : ℝ) (habc : x*y*z = 1) :
    (x + 1)/(x^2 + x + 1) + (y + 1)/(y^2 + y + 1) +
      (z + 1)/(z^2 + z + 1) ≤ 2 := by
  let A := x^2 + x + 1
  let B := y^2 + y + 1
  let C := z^2 + z + 1
  have hA : 0 < A := quadratic_pos x
  have hB : 0 < B := quadratic_pos y
  have hC : 0 < C := quadratic_pos z
  have hpoly : 2*A*B*C - ((x+1)*B*C + (y+1)*C*A + (z+1)*A*B) =
      ((x*y-y*z)^2 + (y*z-z*x)^2 + (z*x-x*y)^2)/2 := by
    calc
      _ = ((x*y-y*z)^2 + (y*z-z*x)^2 + (z*x-x*y)^2)/2 +
          (x*y*z-1)*(x+y+z+x*y+y*z+z*x+2*x*y*z+1) := by dsimp [A, B, C]; ring
      _ = _ := by rw [habc]; ring
  have hnum : 0 ≤ 2*A*B*C - ((x+1)*B*C + (y+1)*C*A + (z+1)*A*B) := by
    rw [hpoly]
    positivity
  apply sub_nonneg.mp
  calc
    0 ≤ (2*A*B*C - ((x+1)*B*C + (y+1)*C*A + (z+1)*A*B))/(A*B*C) :=
      div_nonneg hnum (by positivity)
    _ = 2 - ((x+1)/(x^2+x+1) + (y+1)/(y^2+y+1) + (z+1)/(z^2+z+1)) := by
      change _ = 2 - ((x+1)/A + (y+1)/B + (z+1)/C)
      field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
      <;> ring

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (habc : x * y * z = 1) :
    (x + 1) / (x^2 + x + 1) + (y + 1) / (y^2 + y + 1) +
      (z + 1) / (z^2 + z + 1) ≤ 2 :=
  bound_of_product_one x y z habc
