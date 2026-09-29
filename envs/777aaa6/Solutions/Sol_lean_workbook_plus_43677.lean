-- Prove2me | solution 1 for lean_workbook_plus_43677
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:48.909051+00:00
-- url     : https://prove2.me/submissions/f76bd438-4b8a-4092-b45d-79653f834385

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx: x ∈ Set.Icc 0 1) (hy: y ∈ Set.Icc 0 1) (hz: z ∈ Set.Icc 0 1): (x+y+z)+3*x*y*z ≥ 2*(x*y + y*z + z*x) := by
  rcases hx with ⟨hx0,hx1⟩
  rcases hy with ⟨hy0,hy1⟩
  rcases hz with ⟨hz0,hz1⟩
  have h1 := mul_nonneg (mul_nonneg hx0 (sub_nonneg.mpr hy1)) (sub_nonneg.mpr hz1)
  have h2 := mul_nonneg (mul_nonneg hy0 (sub_nonneg.mpr hz1)) (sub_nonneg.mpr hx1)
  have h3 := mul_nonneg (mul_nonneg hz0 (sub_nonneg.mpr hx1)) (sub_nonneg.mpr hy1)
  nlinarith
