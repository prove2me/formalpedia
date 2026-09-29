-- Prove2me | solution 1 for Teichmuller.teichDist_comm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:53.134359+00:00
-- url     : https://prove2.me/submissions/8c0d0c08-5942-4d4f-852d-880828246db0

-- Sol generated from Geometry/Teichmuller/TorusSpace.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC
import Definitions.Def_Geometry_Teichmuller_TorusSpace
import Theorems.Thm_Teichmuller_LinMap_dil_inv
import Theorems.Thm_Teichmuller_affine_inv
/-
# The Teichmüller space of the torus, and its Teichmüller metric

A marked complex torus is `ℂ / (ℤ + ℤτ)` with `τ` in the upper half plane `ℍ`; the marking is
the choice of the ordered basis `(1, τ)` of the lattice.  The Teichmüller space of the torus is
therefore `ℍ` itself, and the Teichmüller distance between `τ` and `τ'` is
`(1/2) log K`, where `K` is the smallest dilatation of a quasiconformal homeomorphism
`ℂ/Λ_τ → ℂ/Λ_{τ'}` respecting the marking.  For the torus the extremal map is the *affine*
one, the unique `ℝ`-linear map with `1 ↦ 1` and `τ ↦ τ'`, built here as `Teichmuller.affine`.

The results in this file are:

* `Teichmuller.affine_apply_one`, `Teichmuller.affine_apply_tau`: the affine marked map;
* `Teichmuller.eq_affine_of_marked`: **uniqueness** — any real-linear map realizing the marking
  is the affine one, hence (`Teichmuller.dil_affine_le`) it is the extremal one;
* `Teichmuller.affine_comp`, `Teichmuller.affine_inv`: the marked affine maps form a groupoid;
* `Teichmuller.teichDist_triangle`, `teichDist_comm`, `teichDist_eq_zero_iff`:
  the Teichmüller distance is a metric, proved *intrinsically* from quasiconformal
  submultiplicativity (`LinMap.dil_comp_le`) rather than by transport;
* `Teichmuller.teichDist_eq_half_dist` : **the main theorem** — the Teichmüller metric on the
  Teichmüller space of the torus is exactly one half of the hyperbolic (Poincaré) metric of
  curvature `-1` on `ℍ`; equivalently, the Teichmüller metric has curvature `-4`.

The main theorem is a genuine cross-domain identity: the left-hand side is defined by an
extremal problem for quasiconformal distortion (analysis), the right-hand side by the
`SL(2,ℝ)`-invariant Riemannian metric (hyperbolic geometry).  The bridge is the exact formula

    K(τ, τ') = (‖τ' - conj τ‖ + ‖τ' - τ‖)² / (4 · im τ · im τ')

together with the Pythagoras-type identity `‖τ' - conj τ‖² = ‖τ' - τ‖² + 4 · im τ · im τ'`.

-- !-- Lab Notes -- !--
Hypothesizer: `d_T = (1/2) d_ℍ` on the torus, i.e. the Teichmüller metric of the once-marked
torus is a *rescaled* hyperbolic metric, and the rescaling constant is exactly 2 (not 1).
Experimenter: computing `cosh` of both sides is the decisive experiment: `cosh (log K)` equals
`(K + K⁻¹)/2 = (p² + q²)/(p² - q²)` with `p = ‖τ' - conj τ‖`, `q = ‖τ' - τ‖`, while Mathlib's
`UpperHalfPlane.cosh_dist` gives `1 + q²/(2 y y')`; the reflection identity `p² - q² = 4 y y'`
makes them equal.  Analyst: the factor `1/2` is forced — one cannot rescale it away without
breaking `K = 1 ↔ τ = τ'` — and it is the reason the Teichmüller metric of the torus has
curvature `-4`, matching Royden's theorem that Teichmüller metric = Kobayashi metric.
-/

open Teichmuller

open Complex UpperHalfPlane

variable (τ τ' τ'' : ℍ)

























open Teichmuller in
theorem solution: teichDist τ τ' = teichDist τ' τ := by
  rw [teichDist, teichDist, ← affine_inv τ τ', LinMap.dil_inv]
