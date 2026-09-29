-- Prove2me | solution 1 for Teichmuller.LinMap.toFun_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:18:03.925625+00:00
-- url     : https://prove2.me/submissions/03d382f4-5738-49c4-a386-f252e0df4cff

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
























theorem toFun_sub (x y : ℂ) : f.toFun (x - y) = f.toFun x - f.toFun y := by
  simp only [toFun, map_sub]
  ring







open Teichmuller.LinMap in
theorem solution: Function.Injective f.toFun := by
  intro x y hxy
  have h0 : f.toFun (x - y) = 0 := by rw [toFun_sub, hxy, sub_self]
  have hw : f.a * (x - y) = -(f.b * (starRingEnd ℂ) (x - y)) := by
    simp only [toFun] at h0
    linear_combination h0
  have hnorm : ‖f.a‖ * ‖x - y‖ = ‖f.b‖ * ‖x - y‖ := by
    have h := congrArg norm hw
    rw [norm_mul, norm_neg, norm_mul, RCLike.norm_conj] at h
    exact h
  have hz : ‖x - y‖ = 0 := by
    rcases eq_or_lt_of_le (norm_nonneg (x - y)) with h | h
    · exact h.symm
    · nlinarith [f.norm_lt]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)
