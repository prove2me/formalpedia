-- Prove2me | Theorems.Thm_MovingSofa_IsMovingSofa_isPaperMotion
-- name    : MovingSofa.IsMovingSofa.isPaperMotion
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T21:42:28.328391+00:00
-- url     : https://prove2.me/theorems/bf030028-b2ef-4f7c-9239-e7846204e52d
-- title:
--   Canonical motions are paper motions
-- statement:
--   Every canonical hallway motion satisfies the paper motion axioms. Reduction over rotation existence.
-- source:
--   Motion/CanonicalBridge.lean

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Motion_Paper
open Set
open scoped unitInterval

namespace MovingSofa

namespace IsMovingSofa

theorem isPaperMotion {s : Set Point} {m : I → Point ≃ᵃⁱ[ℝ] Point}
    (h : IsMovingSofa s m) : IsPaperMotion s m := by sorry

end IsMovingSofa

end MovingSofa
