-- Prove2me | Theorems.Thm_BerggrenStars_mB_iterate_growth
-- name    : BerggrenStars.mB_iterate_growth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:25:18.845142+00:00
-- url     : https://prove2.me/theorems/99f5fcdf-33f5-4bfd-8a77-b87e9b656ed0
-- title:
--   The `mB`-flow is exponential: `c_k ≥ 3^k c₀`.
-- statement:
--   The `mB`-flow is exponential: `c_k ≥ 3^k c₀`.  (Contrast `mC_iterate_hyp`, where the
--   hypotenuse only grows quadratically.)
--
--   ```lean
--   theorem BerggrenStars.mB_iterate_growth{a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℕ) :
--       3 ^ k * c ≤ (mB^[k] (a, b, c)).2.2 ∧
--         0 < (mB^[k] (a, b, c)).1 ∧ 0 < (mB^[k] (a, b, c)).2.1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/BerggrenHyperbolicStars.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/BerggrenHyperbolicStars.lean#L241

-- Thm stub generated from MachineLearning/BerggrenHyperbolicStars.lean
import Mathlib
import Definitions.Def_MachineLearning_BerggrenHyperbolicStars

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

open BerggrenStars







/-! ### The three Berggren generators -/





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

theorem BerggrenStars.mB_iterate_growth{a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℕ) :
    3 ^ k * c ≤ (mB^[k] (a, b, c)).2.2 ∧
      0 < (mB^[k] (a, b, c)).1 ∧ 0 < (mB^[k] (a, b, c)).2.1 := by sorry
