-- Prove2me | Definitions.Def_Geometry_Teichmuller_Geodesic
-- name    : Geometry_Teichmuller_Geodesic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:59:47.731843+00:00
-- url     : https://prove2.me/theorems/7eac7c04-03df-49d2-86ab-87d93e572d0d
-- title:
--   Aether Catalog definitions — Geometry_Teichmuller_Geodesic
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Teichmuller.Geodesic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Teichmuller/Geodesic.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_Teichmuller_TorusSpace
/-
# Teichmüller geodesics: the stretch line of the torus

A *Teichmüller geodesic* is a family of marked surfaces obtained by stretching a fixed flat
structure in one direction at exponential rate.  For the torus the stretch line based at the
square torus is `t ↦ i e^{2t}`, i.e. the imaginary axis of the Teichmüller space `ℍ`
traversed at exponential speed.

This file shows that this line is a **unit-speed geodesic of the Teichmüller metric**:

* `Teichmuller.teichDist_stretchLine` : `d_T (σ_s, σ_t) = |t - s|`;
* `Teichmuller.teichDist_stretchLine_add` : additivity along the line for `r ≤ s ≤ t`, i.e.
  the triangle inequality of `Teichmuller.teichDist_triangle` is an equality — the line is a
  geodesic, not merely a rectifiable path;
* `Teichmuller.dil_stretchLine` : the extremal quasiconformal dilatation between two points of
  the line is `e^{2|t-s|}`, so the *dilatation* grows exponentially in the Teichmüller distance;
* `Teichmuller.teichDist_unbounded` : the Teichmüller space of the torus has infinite diameter.

-- !-- Lab Notes -- !--
Hypothesizer: the exponential parametrization `i e^{2t}` (not `i e^{t}`) should be the unit-speed
one, because the Teichmüller metric is *half* the hyperbolic metric.
Experimenter: `dist_of_re_eq` gives `d_ℍ (i e^{2s}, i e^{2t}) = |2t - 2s|`, and halving gives
`|t - s|`; the exponent `2` is exactly the factor `1/2` of `teichDist_eq_half_dist` in disguise.
Analyst: the extremal map between `σ_s` and `σ_t` is the diagonal stretch with dilatation
`e^{2|t-s|}` — dilatation is exponential in Teichmüller distance, the quantitative reason
Teichmüller distance is a *logarithm* of a dilatation.
-/

namespace Teichmuller

open Complex UpperHalfPlane

/-- The Teichmüller stretch line through the square torus: the torus `ℂ / ⟨1, i e^{2t}⟩`. -/
noncomputable def stretchLine (t : ℝ) : ℍ :=
  ⟨⟨0, Real.exp (2 * t)⟩, Real.exp_pos _⟩







end Teichmuller


