-- Prove2me | solution 1 for MovingSofa.continuous_motion_linear_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:13:05.319806+00:00
-- url     : https://prove2.me/submissions/f653b290-98c5-4bf2-906a-5190baf49e44

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Mathlib
open Set
open scoped unitInterval
open MovingSofa in
theorem solution (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (x : Point) :
    Continuous (fun t ↦ (m t).linearIsometryEquiv x) := by
  have hev : ∀ y : Point, Continuous fun t => m t y := by
    intro y
    have h1 : Continuous fun t => (m t).toAffineIsometry.toContinuousAffineMap.toContinuousMap :=
      (continuous_induced_dom).comp hm
    have h2 : Continuous fun f : C(Point, Point) => f y := by
      first
        | exact continuous_eval_const y
        | exact ContinuousMap.continuous_eval_const y
    exact h2.comp h1
  have hlin : ∀ t, (m t).linearIsometryEquiv x = m t x - m t 0 := by
    intro t
    have h := (m t).map_vadd 0 x
    rw [vadd_eq_add, vadd_eq_add, add_zero] at h
    rw [h, add_sub_cancel_right]
  simp_rw [hlin]
  exact (hev x).sub (hev 0)
