-- Prove2me | solution 1 for lean_workbook_plus_73635
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:03:07.403625+00:00
-- url     : https://prove2.me/submissions/ab4614ba-d7e7-4299-8baf-833b767c00f3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0)(hab : x * y * z = 1) (h : x^2*y + y^2*z + z^2*x = 3): 1/x + 1/y + 1/z >= 3 := by
  clear hab
  rcases hx with ⟨hx,hy,hz⟩
  have hAMGM (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) : 27*u*v*w ≤ (u+v+w)^3 := by
    nlinarith only [mul_nonneg (sq_nonneg (u+v-2*w)) (show 0 ≤ u+v+w/4 by positivity), mul_nonneg hw (sq_nonneg (u-v))]
  have hA := hAMGM (x^2*y) (y^2*z) (z^2*x) (by positivity) (by positivity) (by positivity)
  rw [h] at hA
  let p := x*y*z
  have hp : 0 < p := by dsimp [p]; positivity
  have hp3 : p^3 ≤ 1 := by dsimp [p]; nlinarith only [hA]
  have hp1 : p ≤ 1 := by
    by_contra hn
    have ht : 0 < p-1 := by linarith
    have hc : 0 < p^2+p+1 := by positivity
    nlinarith only [hp3,mul_pos ht hc]
  have he : (1/x)*(1/y)*(1/z)=1/p := by
    dsimp [p]
    field_simp [ne_of_gt hx,ne_of_gt hy,ne_of_gt hz] <;> ring
  have hprod : 1 ≤ (1/x)*(1/y)*(1/z) := by
    rw [he]
    apply (le_div_iff₀ hp).2
    simpa only [one_mul] using hp1
  have hR := hAMGM (1/x) (1/y) (1/z) (by positivity) (by positivity) (by positivity)
  by_contra hn
  have ht : 0 < 3-(1/x+1/y+1/z) := by linarith
  have hc : 0 < (1/x+1/y+1/z)^2+3*(1/x+1/y+1/z)+9 := by positivity
  nlinarith only [hR,hprod,mul_pos ht hc]
