-- Prove2me | solution 1 for lean_workbook_plus_47398
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:54:09.960816+00:00
-- url     : https://prove2.me/submissions/0c1876cc-a59c-4877-a844-e960873a5334

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c / a + a / b + b / c = -3 / 2) :
  b^2 / a^2 + c^2 / b^2 + a^2 / c^2 ≥ 9 / 4 := by
  clear h₁
  have hAMGM (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hp : u*v*w=1) : 3 ≤ u+v+w := by
    have hA : 27*u*v*w ≤ (u+v+w)^3 := by
      nlinarith only [mul_nonneg (sq_nonneg (u+v-2*w)) (show 0 ≤ u+v+w/4 by positivity), mul_nonneg hw (sq_nonneg (u-v))]
    by_contra hn
    have ht : 0 < 3-(u+v+w) := by linarith
    have hc : 0 < (u+v+w)^2+3*(u+v+w)+9 := by positivity
    have hprod := mul_pos ht hc
    nlinarith only [hA,hprod,hp]
  have hcyclic (r s t : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) : 3 ≤ s^2/r^2+t^2/s^2+r^2/t^2 := by
    apply hAMGM (s^2/r^2) (t^2/s^2) (r^2/t^2) (by positivity) (by positivity) (by positivity)
    field_simp [hr,hs,ht] <;> ring
  have hsource (r s t : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) :
      3 ≤ s^2/r^2+t^2/s^2+r^2/t^2 ∧
      3 ≤ t^2/r^2+r^2/s^2+s^2/t^2 ∧
      6 ≤ s^2/r^2+t^2/s^2+r^2/t^2+t^2/r^2+r^2/s^2+s^2/t^2 := by
    have hF := hcyclic r s t hr hs ht
    have hR := hcyclic r t s hr ht hs
    exact ⟨hF, by linarith only [hR], by linarith only [hF,hR]⟩
  rcases h₀ with ⟨ha,hb,hc⟩
  have hstrong := (hsource a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)).1
  linarith only [hstrong]
