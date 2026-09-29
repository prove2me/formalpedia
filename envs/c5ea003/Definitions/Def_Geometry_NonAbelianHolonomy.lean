-- Prove2me | Definitions.Def_Geometry_NonAbelianHolonomy
-- name    : Geometry_NonAbelianHolonomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:10.077768+00:00
-- url     : https://prove2.me/theorems/3f7f7428-e9dc-48a7-b903-9989ece7369d
-- title:
--   Aether Catalog definitions — Geometry_NonAbelianHolonomy
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.NonAbelianHolonomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/NonAbelianHolonomy.lean by skeleton subtraction
import Mathlib

/-!
# Impossible Figures VI: non-abelian holonomy and rotational developability

The previous files in this thread
(`Geometry.CellularDevelopability`, `Geometry.CycleCertificates`,
`Geometry.GridCertificates`, `Geometry.TwistedDevelopability`) classify *additive*
increment fields: an increment field `ω : E → A` with values in an abelian group is
developable iff its cellular curvature vanishes and its periods vanish on a
generating family of one-cycles.

Direction 5 of the previous cycle observed that additive height integrability is only
the "shadow" of a genuinely geometric realisation problem: for a piecewise linear
developable realisation in three-space the increments are *rotations*, and they
compose non-commutatively.  This file carries out the first testable step listed
there: the **non-abelian Poincaré lemma**.

## Setup

* A combinatorial one-skeleton is a pair of maps `s t : E → V` (source, target).
* A *step* is a pair `(b, e) : Bool × E`: the edge `e` traversed forwards (`b = true`)
  or backwards (`b = false`).
* A *walk* from `a` to `b` is a list of steps, chained by `IsWalk`.
* An increment field with values in a (possibly non-abelian) group `G` is a map
  `ω : E → G`; its **holonomy** `hol ω l` along a walk is the ordered product of the
  steps, later steps multiplying on the left.
* `Developable s t ω` means `ω` is a coboundary: `ω e = H (t e) * (H (s e))⁻¹`.

## Main results

* `hol_of_coboundary` — discrete Stokes: the holonomy of a coboundary along a walk
  from `a` to `b` is `H b * (H a)⁻¹`; in particular closed walks have trivial
  holonomy (`hol_eq_one_of_developable`).
* `developable_iff_holonomy_trivial` — the non-abelian Poincaré lemma: on a connected
  one-skeleton, `ω` is developable **iff** every closed walk based at a fixed vertex
  has trivial holonomy.
* `hol_gauge` / `holonomy_conj_of_gauge` — the holonomy of a gauge-transformed field
  is conjugate to the original; so the *conjugacy class* of the holonomy of a closed
  walk is a gauge invariant, the non-abelian replacement for `period_gauge_invariant`.
* `hol_map` — a group homomorphism `φ : G →* G'` transports holonomy; hence an
  additive obstruction (a nonzero period after abelianisation) is a special case of a
  non-abelian one (`not_developable_of_map_holonomy_ne_one`).
* `triangle_developable_iff` and `penrose_rotational_not_developable`: on the
  three-cycle (the underlying loop of the Penrose triangle) developability is
  equivalent to the triviality of the single product `ω 2 * ω 1 * ω 0`, and the field
  which turns each beam by one and the same transposition of `Equiv.Perm (Fin 3)`
  is not developable — an impossible figure whose obstruction is purely rotational
  and invisible to any abelian period.
-/

namespace ImpossibleFigures.NonAbelian

variable {V E G G' : Type*} [Group G] [Group G']

/-! ## Steps and walks -/

/-- The initial vertex of a step: `(true, e)` starts at `s e`, `(false, e)` at `t e`. -/
def stepStart (s t : E → V) (p : Bool × E) : V := cond p.1 (s p.2) (t p.2)

/-- The terminal vertex of a step. -/
def stepEnd (s t : E → V) (p : Bool × E) : V := cond p.1 (t p.2) (s p.2)

/-- The group element contributed by a step: `ω e` forwards, `(ω e)⁻¹` backwards. -/
def stepHol (ω : E → G) (p : Bool × E) : G := cond p.1 (ω p.2) (ω p.2)⁻¹


/-- Reversing a single step. -/
def revStep (p : Bool × E) : Bool × E := (!p.1, p.2)




/-- `IsWalk s t a b l`: the list of steps `l` is a walk from `a` to `b`. -/
inductive IsWalk (s t : E → V) : V → V → List (Bool × E) → Prop
  | nil (v : V) : IsWalk s t v v []
  | cons {a b : V} {p : Bool × E} {l : List (Bool × E)} (h : stepStart s t p = a)
      (hw : IsWalk s t (stepEnd s t p) b l) : IsWalk s t a b (p :: l)

/-- The holonomy of `ω` along a walk: later steps multiply on the left. -/
def hol (ω : E → G) : List (Bool × E) → G
  | [] => 1
  | p :: l => hol ω l * stepHol ω p






/-- The reverse walk. -/
def revWalk (l : List (Bool × E)) : List (Bool × E) := (l.map revStep).reverse





/-! ## Developability and discrete Stokes -/

/-- `ω` is *developable* if it is the coboundary of a height (frame) field
`H : V → G`. -/
def Developable (s t : E → V) (ω : E → G) : Prop :=
  ∃ H : V → G, ∀ e, ω e = H (t e) * (H (s e))⁻¹





/-! ## Gauge invariance -/

/-- A gauge transformation of an increment field. -/
def gauge (s t : E → V) (H : V → G) (ω : E → G) : E → G :=
  fun e => H (t e) * ω e * (H (s e))⁻¹




/-! ## Comparison with the additive theory -/




/-! ## The Penrose triangle with rotational increments

`V = E = Fin 3`, `s i = i`, `t i = i + 1`: the three-cycle, the underlying loop of the
Penrose triangle.  The increments are now arbitrary group elements ("the rotation
carrying one beam to the next"). -/

/-- Source map of the three-cycle. -/
def triS : Fin 3 → Fin 3 := id

/-- Target map of the three-cycle. -/
def triT : Fin 3 → Fin 3 := fun i => i + 1

/-- The fundamental loop of the three-cycle, based at `0`. -/
def triLoop : List (Bool × Fin 3) := [(true, 0), (true, 1), (true, 2)]








end ImpossibleFigures.NonAbelian


