-- Prove2me | solution 1 for MovingSofa.IsMovingSofa.isPaperMotion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-04T22:03:21.218246+00:00
-- url     : https://prove2.me/submissions/7b58e0c7-7e23-4fd9-b8cd-31343097889d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Motion_Paper
import Theorems.Thm_MovingSofa_exists_motion_rotation

set_option autoImplicit false

noncomputable section

open Set
open scoped unitInterval
open MovingSofa

theorem solution {s : Set MovingSofa.Point} {m : I → MovingSofa.Point ≃ᵃⁱ[ℝ] MovingSofa.Point}
    (h : MovingSofa.IsMovingSofa s m) : MovingSofa.IsPaperMotion s m :=
  ⟨h.isConnected, h.isClosed, h.continuous, ⟨0, fun p => by simp [h.zero]⟩,
    MovingSofa.exists_motion_rotation m h.continuous h.zero, by simpa [h.zero] using h.initial,
    h.subset_hallway, h.final⟩
