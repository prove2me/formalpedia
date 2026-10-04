-- Prove2me | solution 1 for MovingSofa.motion_linear_det_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:57:09.968913+00:00
-- url     : https://prove2.me/submissions/f80ac36b-0775-4bcf-9240-38f26e2f43d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Theorems.Thm_MovingSofa_continuous_motion_linear_apply

set_option autoImplicit false

noncomputable section

open Set
open scoped unitInterval
open MovingSofa

theorem solution (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    0 < LinearMap.det (m t).linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  let L : I → Point →L[ℝ] Point := fun t ↦ (m t).linearIsometryEquiv.toContinuousLinearEquiv
  have hL : Continuous L := continuous_clm_apply.mpr
    (MovingSofa.continuous_motion_linear_apply m hm)
  have hdet : Continuous (fun t ↦ (L t).det) := ContinuousLinearMap.continuous_det.comp hL
  have hne (u : I) : (L u).det ≠ 0 := (m u).linearIsometryEquiv.toLinearEquiv.isUnit_det'.ne_zero
  have hL0 : L 0 = ContinuousLinearMap.id ℝ Point := by
    ext x
    simp only [L, hzero]
    rfl
  have hzero' : (L 0).det = 1 := by rw [hL0]; simp [ContinuousLinearMap.det]
  change 0 < (L t).det
  by_contra hneg
  have hle : (L t).det ≤ 0 := le_of_not_gt hneg
  obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hdet ⟨hle, by rw [hzero']; norm_num⟩
  exact hne u hu
