-- Prove2me | solution 1 for Teichmuller.LinMap.dil_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:38:30.318487+00:00
-- url     : https://prove2.me/submissions/22ca0240-4143-455f-befd-7a5625d58755

-- Sol generated from Geometry/Teichmuller/LinearQC.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC
/-
# Quasiconformal dilatation of real-linear maps of the plane

This file develops, from scratch, the *infinitesimal* layer of Teichmüller theory: the
quasiconformal dilatation of an orientation-preserving, nonsingular `ℝ`-linear map of `ℂ`.

Every `ℝ`-linear map `f : ℂ → ℂ` has the unique normal form

    f z = a * z + b * conj z ,          a b : ℂ,

with Jacobian determinant `‖a‖² - ‖b‖²`; the map is orientation preserving and invertible
exactly when `‖b‖ < ‖a‖`.  Its *Beltrami coefficient* is `μ = b / a` and its *dilatation* is

    K f = (‖a‖ + ‖b‖) / (‖a‖ - ‖b‖) = (1 + ‖μ‖) / (1 - ‖μ‖),

the ratio of the major to the minor axis of the ellipse `f '' (unit circle)`.

The mathematical core of the file is the exact **determinant identity**

    ‖A‖² - ‖B‖² = (‖a‖² - ‖b‖²) * (‖c‖² - ‖d‖²)

for the composite `(A, B)` of `(a, b)` and `(c, d)` (`LinMap.normSq_sub_normSq_comp`), which
combined with the crude triangle bound `‖A‖ + ‖B‖ ≤ (‖a‖ + ‖b‖)(‖c‖ + ‖d‖)` yields
**submultiplicativity of the dilatation** `K (f ∘ g) ≤ K f * K g` through the identity
`K = (‖a‖ + ‖b‖)² / (‖a‖² - ‖b‖²)`.  This is the statement that makes `log K` a metric
downstream (`Geometry.Teichmuller.TorusSpace`).

Main results:

* `LinMap.one_le_dil` : dilatation is at least `1`;
* `LinMap.dil_eq_one_iff` : dilatation `1` ⇔ the map is conformal (`ℂ`-linear);
* `LinMap.comp_apply` : the composition formula is correct as maps of `ℂ`;
* `LinMap.dil_comp_le` : `K (f ∘ g) ≤ K f * K g`;
* `LinMap.dil_inv` : `K (f⁻¹) = K f`, and `LinMap.inv_apply` verifies the inverse formula;
* `LinMap.dil_eq_beltrami` : `K = (1 + ‖μ‖) / (1 - ‖μ‖)`.

-- !-- Lab Notes -- !--
Hypothesizer: the submultiplicativity `K(f∘g) ≤ K(f)K(g)` — the axiom that makes the
Teichmüller metric a metric — should be a purely algebraic identity, not an analytic estimate.
Experimenter: the naive bound `‖A‖ - ‖B‖ ≥ (‖a‖-‖b‖)(‖c‖-‖d‖)` is FALSE termwise (the triangle
inequality loses `2‖b‖‖d‖`); the repair is to bound the *product* `(‖A‖-‖B‖)(‖A‖+‖B‖)` exactly:
the cross terms `2Re(a c conj b conj d)` in `‖A‖²` and `‖B‖²` cancel identically, giving the
determinant identity.  Analyst: the lost factor is exactly the multiplicativity of the Jacobian;
the correct formulation of `K` for the estimate is `K = (‖a‖+‖b‖)²/(‖a‖²-‖b‖²)`, i.e. "square of
an operator norm over a determinant", which is the shape that composes.
-/

open Teichmuller

open Complex


open LinMap

variable (f g : LinMap)








theorem sub_pos' : 0 < ‖f.a‖ - ‖f.b‖ := sub_pos.mpr f.norm_lt























namespace Teichmuller.LinMap
theorem sub_pos' : 0 < ‖f.a‖ - ‖f.b‖ := sub_pos.mpr f.norm_lt

end Teichmuller.LinMap

open Teichmuller in
theorem solution: f.dil = 1 ↔ f.b = 0 := by
  rw [dil, div_eq_one_iff_eq f.sub_pos'.ne']
  constructor
  · intro h
    have : ‖f.b‖ = 0 := by linarith
    simpa using this
  · intro h; simp [h]
