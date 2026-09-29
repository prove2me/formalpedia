-- Prove2me | Definitions.Def_Geometry_Teichmuller_LinearQC
-- name    : Geometry_Teichmuller_LinearQC
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:58:17.982694+00:00
-- url     : https://prove2.me/theorems/0e7cd228-bc36-4a9e-b38b-f3c79422e3b9
-- title:
--   Aether Catalog definitions — Geometry_Teichmuller_LinearQC
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Teichmuller.LinearQC`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Teichmuller/LinearQC.lean by skeleton subtraction
import Mathlib
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

namespace Teichmuller

open Complex

/-- An orientation-preserving, nonsingular `ℝ`-linear self-map of `ℂ`, in the normal form
`z ↦ a * z + b * conj z`.  Nonsingularity and orientation-preservation are encoded by
`‖b‖ < ‖a‖`, i.e. positivity of the Jacobian `‖a‖² - ‖b‖²`. -/
structure LinMap where
  a : ℂ
  b : ℂ
  norm_lt : ‖b‖ < ‖a‖

namespace LinMap

variable (f g : LinMap)

/-- The underlying map `ℂ → ℂ`. -/
def toFun (z : ℂ) : ℂ := f.a * z + f.b * (starRingEnd ℂ) z



/-- The Jacobian determinant `‖a‖² - ‖b‖²`, positive by assumption. -/
noncomputable def jac : ℝ := ‖f.a‖ ^ 2 - ‖f.b‖ ^ 2

theorem jac_pos : 0 < f.jac := by
  have h := f.norm_lt
  have := norm_nonneg f.b
  simp only [jac]
  nlinarith

/-- The dilatation `K = (‖a‖ + ‖b‖)/(‖a‖ - ‖b‖)`: the eccentricity of the image of the unit
circle. -/
noncomputable def dil : ℝ := (‖f.a‖ + ‖f.b‖) / (‖f.a‖ - ‖f.b‖)

/-- The Beltrami coefficient `μ = b / a`. -/
noncomputable def beltrami : ℂ := f.b / f.a








/-- Composition of two real-linear maps, in normal form. -/
noncomputable def comp : LinMap where
  a := f.a * g.a + f.b * (starRingEnd ℂ) g.b
  b := f.a * g.b + f.b * (starRingEnd ℂ) g.a
  norm_lt := by
    set A := f.a * g.a + f.b * (starRingEnd ℂ) g.b with hA
    set B := f.a * g.b + f.b * (starRingEnd ℂ) g.a with hB
    have key : ‖A‖ ^ 2 - ‖B‖ ^ 2 = (‖f.a‖ ^ 2 - ‖f.b‖ ^ 2) * (‖g.a‖ ^ 2 - ‖g.b‖ ^ 2) := by
      simp only [hA, hB, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
      ring
    have hf := f.jac_pos
    have hg := g.jac_pos
    simp only [jac] at hf hg
    have hpos : 0 < ‖A‖ ^ 2 - ‖B‖ ^ 2 := by rw [key]; positivity
    nlinarith [norm_nonneg A, norm_nonneg B]






/-- The inverse map, again in normal form. -/
noncomputable def inv : LinMap where
  a := (starRingEnd ℂ) f.a / (f.jac : ℂ)
  b := -f.b / (f.jac : ℂ)
  norm_lt := by
    have hj : (0:ℝ) < f.jac := f.jac_pos
    have h : ‖((f.jac : ℝ) : ℂ)‖ = f.jac := by
      simp [Complex.norm_real, abs_of_pos hj]
    simp only [norm_div, norm_neg, RCLike.norm_conj, h]
    have := f.norm_lt
    gcongr








end LinMap

end Teichmuller


