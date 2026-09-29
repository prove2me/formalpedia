-- Prove2me | solution 1 for Teichmuller.goldenRatio_sq_le_stretch
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:08:37.455054+00:00
-- url     : https://prove2.me/submissions/cbda9895-54a8-4511-913d-f5590909feda

-- Sol generated from Geometry/Teichmuller/TranslationLength.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_TorusSpace
import Definitions.Def_Geometry_Teichmuller_TranslationLength
import Theorems.Thm_Teichmuller_three_le_abs_tr
/-
# Displacement of Möbius transformations and Teichmüller translation lengths

This file proves an exact **displacement identity** for the action of `SL(2, R)` (`R` any
commutative ring mapping to `ℝ`; in practice `ℝ` or `ℤ`) on the upper half plane: for
`g = !![a, b; c, d]` of determinant `1` and `z = x + i y ∈ ℍ`,

    cosh (dist z (g • z)) = ((a + d)² - 2)/2 + (c (x² + y²) - (a - d) x - b)² / (2 y²) .

The identity is sharp: the second term is a square divided by a positive number, so the
displacement of `g` is minimized exactly on the *axis* `c(x²+y²) - (a-d)x - b = 0`, which is a
nonempty subset of `ℍ` precisely when `g` is hyperbolic (`|tr g| > 2`).  This gives the
**translation length**

    inf_z dist (z, g z) = arcosh (((tr g)² - 2)/2) = 2 log λ(g),
    λ(g) = (|tr g| + √((tr g)² - 4)) / 2 ,

attained on the axis.  Translated through `Teichmuller.teichDist_eq_half_dist`, this is the
torus case of the classical theorem of Bers: **the minimal Teichmüller displacement of an
Anosov mapping class equals the logarithm of its stretch factor**,

    min_τ d_T (τ, g · τ) = log λ(g) ,

where `λ(g)` is the larger eigenvalue of `g`, i.e. the dilatation of the associated Anosov
diffeomorphism of the torus.

Main results:

* `Teichmuller.cosh_dist_smul` : the displacement identity;
* `Teichmuller.exists_axis_point` : the axis is nonempty for hyperbolic `g`;
* `Teichmuller.isLeast_dist_smul` : the hyperbolic translation length is attained and equals
  `arcosh (((tr g)² - 2)/2)`;
* `Teichmuller.isLeast_teichDist_smul` : the Teichmüller translation length of an Anosov
  mapping class of the torus equals `log λ(g)`.

-- !-- Lab Notes -- !--
Hypothesizer: the displacement function `z ↦ dist (z, g z)` of a Möbius transformation should
be *exactly* a perfect square over `2y²` plus a constant determined only by the trace — a purely
algebraic statement of the classification elliptic/parabolic/hyperbolic.
Experimenter: writing `P(z) = c z² - (a-d) z - b` (the numerator of `g z - z`), the experiment
`|P(z)|² - y² ((tr g)² - 4) = (c(x²+y²) - (a-d)x - b)²` is a polynomial identity modulo
`ad - bc = 1`, verified by `linear_combination (-4 y²) (det - 1)`.  Analyst: the "constant"
`((tr g)² - 2)/2` is `cosh` of the translation length, so the trace alone determines the
translation length — the cross-domain payoff is that the *arithmetic* of the trace of an
integer matrix computes a *metric* invariant of the moduli space of tori.
-/

open Teichmuller

open Complex UpperHalfPlane Matrix MatrixGroups



variable {R : Type*} [CommRing R] [Algebra R ℝ]








variable {g : SL(2, R)}





















open Teichmuller in
theorem solution(g : SL(2, ℤ)) (ht : 2 < |tr g|) :
    (3 + Real.sqrt 5) / 2 ≤ stretch g := by
  have h3 : 3 ≤ |tr g| := three_le_abs_tr g ht
  have habs : |tr g| ^ 2 = tr g ^ 2 := sq_abs _
  have hdisc : 5 ≤ tr g ^ 2 - 4 := by nlinarith [h3, habs, abs_nonneg (tr g)]
  have hsqrt : Real.sqrt 5 ≤ Real.sqrt (tr g ^ 2 - 4) := Real.sqrt_le_sqrt hdisc
  rw [stretch]
  linarith
