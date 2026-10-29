-- Prove2me | solution 1 for MovingSofa.continuous_rotation_trans_vaddConst
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:12:46.840974+00:00
-- url     : https://prove2.me/submissions/61c580b0-0972-4b32-bfbc-9bc0be76936e

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Mathlib
open Set
open scoped unitInterval
open MovingSofa in
theorem solution {X : Type*} [TopologicalSpace X]
    {θ : X → Real.Angle} {c : X → Point} (hθ : Continuous θ) (hc : Continuous c) :
    Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (c x))) := by
  apply continuous_induced_rng.2
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : Continuous fun q : X × Point =>
      (Real.Angle.cos (θ q.1) • q.2 + Real.Angle.sin (θ q.1) •
        (EuclideanGeometry.o (M := Point)).rightAngleRotation q.2) + c q.1 := by
    have hc' := Real.Angle.continuous_cos.comp (hθ.comp (continuous_fst : Continuous (Prod.fst : X × Point → X)))
    have hs' := Real.Angle.continuous_sin.comp (hθ.comp (continuous_fst : Continuous (Prod.fst : X × Point → X)))
    fun_prop
  refine h.congr fun q => ?_
  simp [Orientation.rotation_apply]
  rfl
