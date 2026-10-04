-- Prove2me | Definitions.Def_MovingSofa_Motion_Paper
-- name    : MovingSofa_Motion_Paper
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-10-03T17:29:02.252488+00:00
-- url     : https://prove2.me/theorems/bdbe1a98-fc4f-4c0c-9f1a-b998574da439
-- title:
--   Paper motion vocabulary
-- statement:
--   Paper motions (allowing an initial translation, orientation-preserving throughout) and paper moving sofas, plus the continuous-affine-map topology instance missing from the revision. From MovingSofa/Motion/Basic.lean.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/Motion/Basic.lean#L10-L20

import Mathlib.Topology.Algebra.ContinuousAffineMap
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation

set_option autoImplicit false

noncomputable section

open Topology
open scoped unitInterval

namespace MovingSofa

/-- Topology on continuous affine maps of the plane, induced from continuous maps.
/// Drift repair: `c5ea003` provides no `TopologicalSpace` instance for `→ᴬ`;
/// `v4.35` does. Inducing from `C(Point, Point)` matches the `E(2)` repair in
/// `Def_MovingSofa_Basic` and coincides on isometries. -/
instance continuousAffineMapTopology : TopologicalSpace (Point →ᴬ[ℝ] Point) :=
  .induced (·.toContinuousMap) inferInstance

/-- A paper motion permits an initial translation and preserves orientation at every time. -/
def IsPaperMotion (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) : Prop :=
  IsConnected s ∧ IsClosed s ∧ Continuous m ∧
    (∃ q : Point, ∀ p, m 0 p = p + q) ∧
    (∀ t, ∃ a : Real.Angle, ∀ p, m t p = rotationMap a p + m t 0) ∧
    m 0 '' s ⊆ horizontalHallway ∧
    (∀ t, m t '' s ⊆ hallway) ∧ m 1 '' s ⊆ verticalHallway

/-- Movability in the paper's translation-invariant convention. -/
def IsPaperMovingSofa (s : Set Point) : Prop :=
  ∃ m, IsPaperMotion s m

end MovingSofa


