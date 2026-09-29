-- Prove2me | Theorems.Thm_Teichmuller_cosh_dist_smul
-- name    : Teichmuller.cosh_dist_smul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:53:53.344626+00:00
-- url     : https://prove2.me/theorems/7d3a1a4b-48ea-4d67-81af-4bd9ba7091d0
-- title:
--   The displacement identity.
-- statement:
--   **The displacement identity.**  `cosh` of the hyperbolic displacement of `z` under a Möbius
--   transformation is a constant depending only on the trace, plus a perfect square supported on the
--   complement of the axis.
--
--   ```lean
--   theorem Teichmuller.cosh_dist_smul(g : SL(2, R)) (z : ℍ) :
--       Real.cosh (dist z (g • z)) = (tr g ^ 2 - 2) / 2 +
--         (entry g 1 0 * (z.re ^ 2 + z.im ^ 2) - (entry g 0 0 - entry g 1 1) * z.re
--           - entry g 0 1) ^ 2 / (2 * z.im ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Teichmuller/TranslationLength.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Teichmuller/TranslationLength.lean#L77

-- Thm stub generated from Geometry/Teichmuller/TranslationLength.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_TorusSpace
import Definitions.Def_Geometry_Teichmuller_TranslationLength
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

theorem Teichmuller.cosh_dist_smul(g : SL(2, R)) (z : ℍ) :
    Real.cosh (dist z (g • z)) = (tr g ^ 2 - 2) / 2 +
      (entry g 1 0 * (z.re ^ 2 + z.im ^ 2) - (entry g 0 0 - entry g 1 1) * z.re
        - entry g 0 1) ^ 2 / (2 * z.im ^ 2) := by sorry
