-- Prove2me | solution 1 for MovingSofa.inner_le_supportValue_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-05T00:43:38.481319+00:00
-- url     : https://prove2.me/submissions/f2bea1fe-4667-4568-b092-0098422e1245

import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Plane
noncomputable section
open MovingSofa


/-- Every point of a compact set lies below its support value. -/
theorem solution {s : Set Point}
    (hs : IsCompact s) {p : Point} (hp : p ∈ s) (a : Real.Angle) :
    inner ℝ p (normalVector a) ≤ supportValue s a := by
  apply le_csSup (hs.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
  exact ⟨p, hp, rfl⟩
