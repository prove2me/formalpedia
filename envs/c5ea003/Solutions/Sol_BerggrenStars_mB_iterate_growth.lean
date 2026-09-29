-- Prove2me | solution 1 for BerggrenStars.mB_iterate_growth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:08:58.470612+00:00
-- url     : https://prove2.me/submissions/93efc5a1-8e32-47d8-be1d-2fa252aeb258

-- Sol generated from MachineLearning/BerggrenHyperbolicStars.lean
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




/-! ### Sanity checks against the concrete tree -/





open BerggrenStars in
theorem solution{a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℕ) :
    3 ^ k * c ≤ (mB^[k] (a, b, c)).2.2 ∧
      0 < (mB^[k] (a, b, c)).1 ∧ 0 < (mB^[k] (a, b, c)).2.1 := by
  induction k with
  | zero => simpa using ⟨ha, hb⟩
  | succ n ih =>
      obtain ⟨hgrow, hpos1, hpos2⟩ := ih
      have hcn : 0 < (mB^[n] (a, b, c)).2.2 := by
        have : (0:ℤ) < 3 ^ n * c := by positivity
        omega
      obtain ⟨p, q, r⟩ := (mB^[n] (a, b, c))
      simp only at hpos1 hpos2 hcn hgrow
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_, ?_⟩ <;> simp only [mB]
      · have : (3:ℤ) ^ (n + 1) * c = 3 * (3 ^ n * c) := by ring
        omega
      · omega
      · omega
