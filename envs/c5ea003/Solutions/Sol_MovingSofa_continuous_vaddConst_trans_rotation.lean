-- Prove2me | solution 1 for MovingSofa.continuous_vaddConst_trans_rotation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:12:55.963816+00:00
-- url     : https://prove2.me/submissions/2b70b14f-81bc-4fa7-bd4a-c2810a227e52

import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Mathlib
open Set
open scoped unitInterval
open MovingSofa in
theorem solution :
    Continuous (fun q : Real.Angle × Point ↦ ((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)) := by
  apply continuous_induced_rng.2
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : Continuous fun q : (Real.Angle × Point) × Point =>
      (Real.Angle.cos q.1.1 • (q.2 + q.1.2) + Real.Angle.sin q.1.1 •
        (EuclideanGeometry.o (M := Point)).rightAngleRotation (q.2 + q.1.2)) := by
    have hc' := Real.Angle.continuous_cos.comp
      ((continuous_fst : Continuous (Prod.fst : Real.Angle × Point → Real.Angle)).comp
        (continuous_fst : Continuous (Prod.fst : (Real.Angle × Point) × Point → Real.Angle × Point)))
    have hs' := Real.Angle.continuous_sin.comp
      ((continuous_fst : Continuous (Prod.fst : Real.Angle × Point → Real.Angle)).comp
        (continuous_fst : Continuous (Prod.fst : (Real.Angle × Point) × Point → Real.Angle × Point)))
    fun_prop
  refine h.congr fun q => ?_
  simp [Orientation.rotation_apply]
  rfl
