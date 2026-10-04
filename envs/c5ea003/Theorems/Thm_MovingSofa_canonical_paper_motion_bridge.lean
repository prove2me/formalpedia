-- Prove2me | Theorems.Thm_MovingSofa_canonical_paper_motion_bridge
-- name    : MovingSofa.canonical_paper_motion_bridge
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T20:25:52.420993+00:00
-- url     : https://prove2.me/theorems/7581981b-c878-4cfe-8b53-e1627e5b642c
-- title:
--   Paper and canonical motions are equivalent up to translation
-- statement:
--   Paper and canonical hallway motions are equivalent up to translation, preserving volumes. Source: Motion/CanonicalBridge.lean.
-- source:
--   Motion/CanonicalBridge.lean#L36-L42

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Tactic.FunProp
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Motion_Paper
open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

theorem canonical_paper_motion_bridge :
    (∀ s : Set Point, IsPaperMovingSofa s →
      ∃ (q : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
        IsMovingSofa ((fun p ↦ p + q) '' s) m ∧
        volume ((fun p ↦ p + q) '' s) = volume s) ∧
    (∀ (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point),
      IsMovingSofa s m → IsPaperMovingSofa s) := by sorry

end MovingSofa
