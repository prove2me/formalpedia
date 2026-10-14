-- Prove2me | Definitions.Def_Thurston23_bundle
-- name    : Thurston23_bundle
-- status  : Definition
-- author  : @t4v1
-- created : 2026-09-05T22:52:12.227261+00:00
-- url     : https://prove2.me/theorems/518a08f3-ebf2-48a9-8257-8801eef6d59d
-- title:
--   Hyperbolic 3-space, its volume and distance, Kleinian actions, and the set of volumes
-- statement:
--   Hyperbolic 3-space is the upper half-space; its volume is Lebesgue measure with density z^-3, the Riemannian volume of (dx^2+dy^2+dz^2)/z^2 written out; its distance is given by the closed formula cosh d(p,q) = 1 + |p-q|^2/(2 p_3 q_3). A Kleinian action is a free, properly discontinuous action by hyperbolic isometries preserving that volume. The set of volumes collects the finite positive measures of fundamental domains of such actions.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23.

import Mathlib

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

/-- The upper half-space model of hyperbolic `3`-space. Declared as an
`abbrev` so that the measurable and topological structures of the subtype are
inherited, without naming any auto-generated instance. -/
abbrev H3 : Type := {p : Fin 3 → ℝ // 0 < p 2}

/-- The hyperbolic volume: Lebesgue measure with density `z⁻³`. This is the
Riemannian volume of the metric `(dx² + dy² + dz²)/z²` written out. -/
noncomputable def hvol : Measure H3 :=
  ((volume : Measure (Fin 3 → ℝ)).comap Subtype.val).withDensity
    fun p => ENNReal.ofReal ((p.1 2) ^ (3 : ℕ))⁻¹

/-- The hyperbolic distance, through the closed formula
`cosh d(p,q) = 1 + |p - q|² / (2 p₃ q₃)`, written with the logarithmic form of
`arcosh`. -/
noncomputable def hdist (p q : H3) : ℝ :=
  let c : ℝ := 1 + (∑ i, (p.1 i - q.1 i) ^ 2) / (2 * p.1 2 * q.1 2)
  Real.log (c + Real.sqrt (c ^ 2 - 1))

/-! ## Kleinian groups and the volumes of their quotients -/

/-- A Kleinian action: a group acting on hyperbolic `3`-space by hyperbolic
isometries, freely and properly discontinuously. The quotient by such an action
is a complete hyperbolic `3`-manifold; discreteness and torsion freeness are
consequences of the conditions below rather than extra hypotheses. Preservation
of `hvol` is stated as a field: it is true of every hyperbolic isometry, but
deriving it from `isometry` means classifying `Isom(ℍ³)`, which is not the
subject of this mission. -/
structure IsKleinian (G : Type) [Group G] [MulAction G H3] : Prop where
  /-- each element acts by a hyperbolic isometry -/
  isometry : ∀ (g : G) (p q : H3), hdist (g • p) (g • q) = hdist p q
  /-- each element preserves the hyperbolic volume -/
  measure_preserving : ∀ g : G, MeasurePreserving (fun p : H3 => g • p) hvol hvol
  /-- the action is free: no element except the identity fixes a point -/
  free : ∀ g : G, g ≠ 1 → ∀ p : H3, g • p ≠ p
  /-- the action is properly discontinuous -/
  properly_discontinuous :
    ∀ K : Set H3, IsCompact K → {g : G | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite

/-- The set of volumes of finite-volume hyperbolic `3`-manifolds: the measures
of fundamental domains of Kleinian actions. -/
def hyperbolicVolumes : Set ℝ :=
  {v | ∃ (G : Type) (_ : Group G) (_ : MulAction G H3), IsKleinian G ∧
      ∃ F : Set H3, MeasureTheory.IsFundamentalDomain G F hvol ∧
        hvol F = ENNReal.ofReal v ∧ 0 < v}

end Thurston23


