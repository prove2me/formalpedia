-- Prove2me | solution 1 for ImpossibleFigures.NonAbelian.developable_gauge_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:10.50527+00:00
-- url     : https://prove2.me/submissions/c7fd987d-d9e4-4ebe-843e-6ac6aed0abcd

-- Sol generated from Geometry/NonAbelianHolonomy.lean
import Mathlib
import Definitions.Def_Geometry_NonAbelianHolonomy
import Theorems.Thm_ImpossibleFigures_NonAbelian_developable_iff_holonomy_trivial
import Theorems.Thm_ImpossibleFigures_NonAbelian_hol_gauge

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

open ImpossibleFigures.NonAbelian

variable {V E G G' : Type*} [Group G] [Group G']

/-! ## Steps and walks -/





















/-! ## Developability and discrete Stokes -/






/-! ## Gauge invariance -/



/-- **Gauge invariance of the rotational holonomy.**  On a closed walk the holonomy of
a gauge-transformed field is conjugate to the original holonomy; in particular
"holonomy `= 1`" is a gauge-invariant condition. -/
theorem holonomy_conj_of_gauge {s t : E → V} (H : V → G) (ω : E → G) {a : V}
    {l : List (Bool × E)} (h : IsWalk s t a a l) :
    hol (gauge s t H ω) l = H a * hol ω l * (H a)⁻¹ := hol_gauge H ω h


/-! ## Comparison with the additive theory -/




/-! ## The Penrose triangle with rotational increments

`V = E = Fin 3`, `s i = i`, `t i = i + 1`: the three-cycle, the underlying loop of the
Penrose triangle.  The increments are now arbitrary group elements ("the rotation
carrying one beam to the next"). -/












open ImpossibleFigures.NonAbelian in
theorem solution{s t : E → V} (H : V → G) (ω : E → G) (base : V)
    (hconn : ∀ v : V, ∃ l, IsWalk s t base v l) :
    Developable s t (gauge s t H ω) ↔ Developable s t ω := by
  rw [developable_iff_holonomy_trivial _ base hconn,
    developable_iff_holonomy_trivial _ base hconn]
  constructor
  · intro h l hl
    have := h l hl
    rw [holonomy_conj_of_gauge H ω hl] at this
    have h2 := congrArg (fun g => (H base)⁻¹ * g * H base) this
    simpa [mul_assoc] using h2
  · intro h l hl
    rw [holonomy_conj_of_gauge H ω hl, h l hl]
    simp
