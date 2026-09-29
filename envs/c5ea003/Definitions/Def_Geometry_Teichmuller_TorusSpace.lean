-- Prove2me | Definitions.Def_Geometry_Teichmuller_TorusSpace
-- name    : Geometry_Teichmuller_TorusSpace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:59:07.82337+00:00
-- url     : https://prove2.me/theorems/53bf7610-a31d-45fd-8b1a-ff9d92473220
-- title:
--   Aether Catalog definitions — Geometry_Teichmuller_TorusSpace
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Teichmuller.TorusSpace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Teichmuller/TorusSpace.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC
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

namespace Teichmuller

open Complex UpperHalfPlane

variable (τ τ' τ'' : ℍ)

/-- The complex conjugate of a point of the upper half plane. -/
noncomputable abbrev cbar (τ : ℍ) : ℂ := (starRingEnd ℂ) (τ : ℂ)

theorem sub_cbar_self : (τ : ℂ) - cbar τ = ((2 * τ.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [cbar]
  ring

theorem norm_sub_cbar_self : ‖(τ : ℂ) - cbar τ‖ = 2 * τ.im := by
  rw [sub_cbar_self, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]


/-- The reflection identity: `‖τ' - conj τ‖² = ‖τ' - τ‖² + 4 (im τ)(im τ')`.  This is the exact
form of the statement that `conj τ` is the mirror image of `τ` in the real axis. -/
theorem normSq_sub_cbar :
    ‖(τ' : ℂ) - cbar τ‖ ^ 2 = ‖(τ' : ℂ) - (τ : ℂ)‖ ^ 2 + 4 * τ.im * τ'.im := by
  simp only [cbar, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
  ring

theorem norm_sub_lt_norm_sub_cbar :
    ‖(τ' : ℂ) - (τ : ℂ)‖ < ‖(τ' : ℂ) - cbar τ‖ := by
  have h := normSq_sub_cbar τ τ'
  have h1 : (0:ℝ) < 4 * τ.im * τ'.im := by
    have := τ.im_pos; have := τ'.im_pos; positivity
  nlinarith [norm_nonneg ((τ' : ℂ) - (τ : ℂ)), norm_nonneg ((τ' : ℂ) - cbar τ)]

/-- The **affine marked map** from the torus `ℂ/⟨1, τ⟩` to the torus `ℂ/⟨1, τ'⟩`: the unique
`ℝ`-linear map with `1 ↦ 1` and `τ ↦ τ'`. -/
noncomputable def affine : LinMap where
  a := ((τ' : ℂ) - cbar τ) / ((τ : ℂ) - cbar τ)
  b := ((τ : ℂ) - (τ' : ℂ)) / ((τ : ℂ) - cbar τ)
  norm_lt := by
    rw [norm_div, norm_div]
    have hm : (0:ℝ) < ‖(τ : ℂ) - cbar τ‖ := by
      rw [norm_sub_cbar_self]; have := τ.im_pos; positivity
    have := norm_sub_lt_norm_sub_cbar τ τ'
    rw [show ((τ : ℂ) - (τ' : ℂ)) = -((τ' : ℂ) - (τ : ℂ)) by ring, norm_neg]
    gcongr









/-- The Teichmüller distance on the Teichmüller space `ℍ` of the marked torus: half the
logarithm of the extremal dilatation. -/
noncomputable def teichDist : ℝ := Real.log (affine τ τ').dil / 2








end Teichmuller


