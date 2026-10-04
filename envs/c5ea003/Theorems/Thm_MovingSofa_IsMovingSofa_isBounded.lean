-- Prove2me | Theorems.Thm_MovingSofa_IsMovingSofa_isBounded
-- name    : MovingSofa.IsMovingSofa.isBounded
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T18:09:29.688984+00:00
-- url     : https://prove2.me/theorems/9409051b-f9cc-4ec9-8d07-2d6d364e86dc
-- title:
--   Moving sofas are bounded
-- statement:
--   Every set admitting a hallway motion is bounded.
-- source:
--   x

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Motion_Paper
open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

namespace IsMovingSofa

theorem isBounded {s : Set Point}
    {m : I → Point ≃ᵃⁱ[ℝ] Point} (h : IsMovingSofa s m) : Bornology.IsBounded s := by sorry

end IsMovingSofa

end MovingSofa
