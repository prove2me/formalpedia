-- Prove2me | Definitions.Def_Geometry_TwistedDevelopability
-- name    : Geometry_TwistedDevelopability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:01:06.083418+00:00
-- url     : https://prove2.me/theorems/f396d6d9-0874-425e-bf87-df6133dfc92d
-- title:
--   Aether Catalog definitions — Geometry_TwistedDevelopability
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.TwistedDevelopability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/TwistedDevelopability.lean by skeleton subtraction
import Mathlib

/-!
# Impossible Figures VI: Orientation covers and signed holonomy

*Increment fields twisted by an orientation local system.*

The companion file `Geometry/CellularDevelopability.lean` classifies untwisted
increment fields on an arbitrary two–dimensional cell complex: developability is
equivalent to the vanishing of the period on the whole one–cycle group, hence to
vanishing curvature plus vanishing periods on a generating family of cycles.

This file treats the **twisted** case, which models non-orientable figures (Möbius
strips, Klein bottles) where the height coordinate is only defined up to a sign
that flips along orientation-reversing edges.  An **orientation local system** is
recorded by a weight function `w : E → ℤ` (in the geometric case `w e = ±1`); a
field `ω : E → A` is **twisted developable** when

`ω e = h (t e) - w e • h (s e)`

for some height field `h : V → A`.  The corresponding twisted boundary operator is
`∂ʷ e = [t e] - w e • [s e]`.

## Main results

* `period_eq_zero_of_developableTw` — twisted developability forces the period to
  vanish on every twisted one–cycle.
* `exists_half_period_of_developableTw` — the **anti-invariance condition**: on an
  orientation-reversing loop `ℓ` (a chain with `∂ʷ ℓ = 2 • [v₀]`, the algebraic
  shadow of a loop that lifts to a path between the two sheets of the orientation
  double cover) the period must be *divisible by two* in the coefficient group.
* `developableTw_iff` — **the twisted classification**: with a base point, chains
  joining it to every vertex (with odd sign holonomies) and an orientation-reversing
  loop `ℓ`, a twisted field is developable iff its periods vanish on all twisted
  cycles *and* its period on `ℓ` is twice some coefficient.
* `mobius_periods_insufficient` — a genuine **counterexample** showing the second
  condition is not implied by the first: on the one-vertex, one-edge complex with
  `w = -1` and coefficients `ℤ`, the twisted cycle group is trivial (so all period
  obstructions vanish) yet the unit field `ω ≡ 1` is not developable.  Signed
  holonomy is therefore a strictly new obstruction beyond ordinary cohomology.
-/

namespace ImpossibleFigures.Twisted

variable {V E A : Type*} [AddCommGroup A]

/-! ### Twisted chains and twisted developability -/

/-- The **twisted boundary operator** attached to a weight (orientation) system
`w : E → ℤ`: `∂ʷ e = [t e] - w e • [s e]`.  For `w ≡ 1` this is the usual boundary
map of the one–skeleton. -/
noncomputable def boundaryTw (s t : E → V) (w : E → ℤ) : (E →₀ ℤ) →ₗ[ℤ] (V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun e =>
    Finsupp.single (t e) (1 : ℤ) - w e • Finsupp.single (s e) (1 : ℤ)

/-- The period (holonomy) of an increment field on a one–chain. -/
noncomputable def period (ω : E → A) : (E →₀ ℤ) →ₗ[ℤ] A :=
  Finsupp.linearCombination ℤ ω

/-- **Twisted developability**: `ω` is the coboundary of a height field for the
local system `w`. -/
def DevelopableTw (s t : E → V) (w : E → ℤ) (ω : E → A) : Prop :=
  ∃ h : V → A, ∀ e, ω e = h (t e) - w e • h (s e)



/-! ### Necessary conditions -/




/-! ### The twisted classification -/


/-! ### The Möbius counterexample: signed holonomy beyond periods -/

section Mobius

/-- Source map of the one-vertex, one-edge complex. -/
def mobS : Unit → Unit := fun _ => ()

/-- Target map of the one-vertex, one-edge complex. -/
def mobT : Unit → Unit := fun _ => ()

/-- The orientation local system of the Möbius band: the unique edge reverses
orientation. -/
def mobW : Unit → ℤ := fun _ => -1

/-- The unit increment field on the Möbius complex. -/
def mobOmega : Unit → ℤ := fun _ => 1

/-- The orientation-reversing loop of the Möbius complex: traversing the unique
edge once. Its twisted boundary is `2 • [v₀]`, so it is a path between the two
sheets of the orientation double cover. -/
noncomputable def mobLoop : Unit →₀ ℤ := Finsupp.single () 1






end Mobius

end ImpossibleFigures.Twisted


