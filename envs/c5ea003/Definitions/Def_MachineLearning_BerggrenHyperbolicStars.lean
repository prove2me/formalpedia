-- Prove2me | Definitions.Def_MachineLearning_BerggrenHyperbolicStars
-- name    : MachineLearning_BerggrenHyperbolicStars
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:36:55.93539+00:00
-- url     : https://prove2.me/theorems/7b9a5a7b-3fca-4dc9-8de7-7dc709af3922
-- title:
--   Aether Catalog definitions — MachineLearning_BerggrenHyperbolicStars
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.BerggrenHyperbolicStars`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/BerggrenHyperbolicStars.lean by skeleton subtraction
import Mathlib

/-!
# The Lorentzian skeleton of the Berggren / Barning–Hall tree

## Motivation

Plotting the Berggren tree of primitive Pythagorean triples inside a hyperbolic disc
produces striking visual artefacts: besides the lines that radiate from the centre of
the disc, one sees *stars* — bundles of curves radiating from isolated points **on the
boundary circle**.

This file supplies the algebraic explanation.  A Pythagorean triple `(a,b,c)` is exactly
an integer vector on the light cone of the Lorentzian form

  `Q(a,b,c) = a² + b² − c²`   (signature `(2,1)`).

The three Berggren matrices are integral isometries of `Q`, i.e. elements of the Lorentz
group `O(2,1;ℤ)`, which is the isometry group of the hyperbolic plane in the hyperboloid
(Klein) model.  Plotting a triple in the disc is plotting a null ray, i.e. an *ideal
point* of `H²`.

The visual structure is then governed by the **conjugacy type** of the three generators:

* `mA` and `mC` are **parabolic** (unipotent): each one conserves a nonzero linear
  functional (`c − b` resp. `c − a`) whose vanishing locus is a rational null direction.
  Consequently their orbits crawl along **horocycles** and accumulate at *one rational
  boundary point*, at a quadratic (polynomial) rate.  This is the star.
* `mB` is **hyperbolic**: it only conserves `|a − b|`, whose vanishing locus is the
  *irrational* null direction `(1,1,√2)`.  Its orbits run along a geodesic and reach the
  boundary at an exponential rate.

This file establishes the algebra: Lorentz invariance, the conserved charges, exact
closed forms for the two unipotent flows (the `k`-th iterate is a *quadratic polynomial
in `k`*, the signature of a Jordan block of size 3), positivity/primitivity preservation,
and the exponential growth of the hyperbolic flow.  The analytic consequences (the actual
limits on the boundary circle, the horocyclic star, the tangency law) are in
`MachineLearning.BerggrenHorocycleStars`.

The three matrices agree with the catalog's `B₃` and with the inverse matrices used in
`Shared/BerggrenTrees/Parent_hyp_lt.lean`.
-/

namespace BerggrenStars

/-- Integer vectors of the ambient Lorentzian lattice `ℤ^{2,1}`. -/
abbrev Vec : Type := ℤ × ℤ × ℤ

/-- The Lorentzian bilinear form of signature `(2,1)`:
`⟨v, w⟩ = v₁w₁ + v₂w₂ − v₃w₃`. -/
def bil (v w : Vec) : ℤ := v.1 * w.1 + v.2.1 * w.2.1 - v.2.2 * w.2.2

/-- The associated quadratic form `Q(a,b,c) = a² + b² − c²`. -/
def qform (v : Vec) : ℤ := bil v v

/-- Being on the light cone is exactly being a Pythagorean triple. -/
def OnCone (v : Vec) : Prop := qform v = 0



/-! ### The three Berggren generators -/

/-- First Berggren generator (Barning–Hall matrix `A`). -/
def mA (v : Vec) : Vec :=
  (v.1 - 2 * v.2.1 + 2 * v.2.2, 2 * v.1 - v.2.1 + 2 * v.2.2, 2 * v.1 - 2 * v.2.1 + 3 * v.2.2)

/-- Second Berggren generator (Barning–Hall matrix `B`). -/
def mB (v : Vec) : Vec :=
  (v.1 + 2 * v.2.1 + 2 * v.2.2, 2 * v.1 + v.2.1 + 2 * v.2.2, 2 * v.1 + 2 * v.2.1 + 3 * v.2.2)

/-- Third Berggren generator (Barning–Hall matrix `C`; the catalog's `B₃`). -/
def mC (v : Vec) : Vec :=
  (-v.1 + 2 * v.2.1 + 2 * v.2.2, -2 * v.1 + v.2.1 + 2 * v.2.2, -2 * v.1 + 2 * v.2.1 + 3 * v.2.2)

/-- The root of the tree. -/
def root : Vec := (3, 4, 5)

/-! ### Lorentz invariance: the generators lie in `O(2,1;ℤ)` -/








/-! ### Conserved charges: the linear functionals fixed by each generator

Each generator preserves a linear functional; the boundary point at which its orbits
accumulate is precisely the null direction on which that functional vanishes.  This is
the structural heart of the whole picture. -/









/-! ### Unipotency: `mA` and `mC` are parabolic

The exact closed form of the `k`-th iterate is a *quadratic* polynomial in `k`; this is
the fingerprint of a rank-3 unipotent Jordan block, i.e. of a parabolic isometry of `H²`. -/






/-! ### Positivity, and the boundary charge is positive -/





/-! ### The hyperbolic generator grows exponentially -/




/-! ### Sanity checks against the concrete tree -/




end BerggrenStars


