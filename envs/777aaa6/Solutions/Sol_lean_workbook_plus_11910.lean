-- Prove2me | solution 1 for lean_workbook_plus_11910
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:54:02.363646+00:00
-- url     : https://prove2.me/submissions/a5f2ede3-26ca-4af3-9933-b6c136e0da15

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0 ∧ x*y*z = 1) : x^2 + y^2 + z^2 >= 1/x + 1/y + 1/z := by
  rcases hx with ⟨hx,hy,hz,hxyz⟩
  have h1 : 1/x=y*z := (div_eq_iff (ne_of_gt hx)).mpr (by nlinarith only [hxyz])
  have h2 : 1/y=z*x := (div_eq_iff (ne_of_gt hy)).mpr (by nlinarith only [hxyz])
  have h3 : 1/z=x*y := (div_eq_iff (ne_of_gt hz)).mpr (by nlinarith only [hxyz])
  rw [h1,h2,h3]
  nlinarith only [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
