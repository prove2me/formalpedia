-- Prove2me | solution 1 for Teichmuller.LinMap.dil_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:34:01.691021+00:00
-- url     : https://prove2.me/submissions/ea69825c-a824-4a8b-bc1f-5a9b8aa9666a

-- Sol generated from Geometry/Teichmuller/LinearQC.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC
import Theorems.Thm_Teichmuller_LinMap_dil_eq_sq_div_jac
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


















/-- **Multiplicativity of the Jacobian**: the exact identity behind submultiplicativity of the
dilatation.  The cross terms `2 Re (a c conj b conj d)` cancel. -/
theorem comp_a (f g : LinMap) : (f.comp g).a = f.a * g.a + f.b * (starRingEnd ℂ) g.b := rfl
theorem comp_b (f g : LinMap) : (f.comp g).b = f.a * g.b + f.b * (starRingEnd ℂ) g.a := rfl
theorem normSq_sub_normSq_comp :
    ‖(f.comp g).a‖ ^ 2 - ‖(f.comp g).b‖ ^ 2 = f.jac * g.jac := by
  simp only [comp_a, comp_b, jac, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

theorem jac_comp : (f.comp g).jac = f.jac * g.jac := normSq_sub_normSq_comp f g












open Teichmuller in
theorem solution: (f.comp g).dil ≤ f.dil * g.dil := by
  have hjac : (f.comp g).jac = f.jac * g.jac := jac_comp f g
  have hsum : ‖(f.comp g).a‖ + ‖(f.comp g).b‖ ≤ (‖f.a‖ + ‖f.b‖) * (‖g.a‖ + ‖g.b‖) := by
    have h1 : ‖f.a * g.a + f.b * (starRingEnd ℂ) g.b‖ ≤ ‖f.a‖ * ‖g.a‖ + ‖f.b‖ * ‖g.b‖ := by
      refine (norm_add_le _ _).trans ?_
      simp
    have h2 : ‖f.a * g.b + f.b * (starRingEnd ℂ) g.a‖ ≤ ‖f.a‖ * ‖g.b‖ + ‖f.b‖ * ‖g.a‖ := by
      refine (norm_add_le _ _).trans ?_
      simp
    simp only [comp_a, comp_b]
    nlinarith [h1, h2]
  rw [dil_eq_sq_div_jac, dil_eq_sq_div_jac, dil_eq_sq_div_jac, hjac, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos f.jac_pos g.jac_pos)]
  have hnn : 0 ≤ ‖(f.comp g).a‖ + ‖(f.comp g).b‖ := by positivity
  nlinarith [hsum, hnn]
