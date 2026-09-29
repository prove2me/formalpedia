-- Prove2me | solution 1 for Teichmuller.cosh_dist_smul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:57:14.387128+00:00
-- url     : https://prove2.me/submissions/e2f871e0-040d-472d-b278-0c65e085959c

-- Sol generated from Geometry/Teichmuller/TranslationLength.lean
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

private lemma div_div_two_mul_aux (Q N y : ℝ) (hN : N ≠ 0) (hy : y ≠ 0) :
    Q / N / (2 * y * (y / N)) = Q / (2 * y ^ 2) := by
  field_simp


variable {R : Type*} [CommRing R] [Algebra R ℝ]



theorem entry_det (g : SL(2, R)) :
    entry g 0 0 * entry g 1 1 - entry g 0 1 * entry g 1 0 = 1 := by
  have h : (g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1
      - (g : Matrix (Fin 2) (Fin 2) R) 0 1 * (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have := congrArg (algebraMap R ℝ) h
  simpa [entry, map_sub, map_mul] using this





variable {g : SL(2, R)}





















open Teichmuller in
theorem solution(g : SL(2, R)) (z : ℍ) :
    Real.cosh (dist z (g • z)) = (tr g ^ 2 - 2) / 2 +
      (entry g 1 0 * (z.re ^ 2 + z.im ^ 2) - (entry g 0 0 - entry g 1 1) * z.re
        - entry g 0 1) ^ 2 / (2 * z.im ^ 2) := by
  set a := entry g 0 0 with ha
  set b := entry g 0 1 with hb
  set c := entry g 1 0 with hc
  set d := entry g 1 1 with hd
  have hdet : a * d - b * c = 1 := entry_det g
  set x := z.re with hx
  set y := z.im with hy
  have hypos : 0 < y := z.im_pos
  have hzre : (z : ℂ).re = x := rfl
  have hzim : (z : ℂ).im = y := rfl
  have hcoe : ((g • z : ℍ) : ℂ) = ((a : ℂ) * z + (b : ℂ)) / ((c : ℂ) * z + (d : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, ha, hb, hc, hd]
    simp [entry]
  have hden : ((c : ℂ) * z + (d : ℂ)) ≠ 0 := by
    intro h
    have h1 : c * y = 0 := by
      have h2 := congrArg Complex.im h
      simpa [Complex.add_im, Complex.mul_im] using h2
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hypos.ne'
    have hd0 : d = 0 := by
      have h2 := congrArg Complex.re h
      simp [hc0] at h2
      exact h2
    rw [hc0, hd0] at hdet
    simp at hdet
  have hNpos : (0:ℝ) < (c * x + d) ^ 2 + (c * y) ^ 2 := by
    rcases eq_or_ne c 0 with h | h
    · have hd0 : d ≠ 0 := by
        intro hd0; rw [h, hd0] at hdet; simp at hdet
      simp [h]
      positivity
    · positivity
  have hNne : ((c * x + d) ^ 2 + (c * y) ^ 2) ≠ 0 := hNpos.ne'
  have hyne : y ≠ 0 := hypos.ne'
  have hN : Complex.normSq ((c : ℂ) * z + (d : ℂ)) = (c * x + d) ^ 2 + (c * y) ^ 2 := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  have hsub : (z : ℂ) - ((g • z : ℍ) : ℂ)
      = ((c : ℂ) * z * z + ((d : ℂ) - (a : ℂ)) * z - (b : ℂ)) / ((c : ℂ) * z + (d : ℂ)) := by
    rw [hcoe, eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
    ring
  have hP : Complex.normSq ((c : ℂ) * z * z + ((d : ℂ) - (a : ℂ)) * z - (b : ℂ))
      = (c * (x ^ 2 - y ^ 2) + (d - a) * x - b) ^ 2 + (2 * c * x * y + (d - a) * y) ^ 2 := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hd2 : dist (z : ℂ) ((g • z : ℍ) : ℂ) ^ 2
      = ((c * (x ^ 2 - y ^ 2) + (d - a) * x - b) ^ 2 + (2 * c * x * y + (d - a) * y) ^ 2)
        / ((c * x + d) ^ 2 + (c * y) ^ 2) := by
    rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq, hsub, Complex.normSq_div, hN, hP]
  have hnum : (((a : ℂ) * z + b) * (starRingEnd ℂ) ((c : ℂ) * z + d)).im = y := by
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]
    linear_combination y * hdet
  have him : (g • z).im = y / ((c * x + d) ^ 2 + (c * y) ^ 2) := by
    have key : ((a : ℂ) * z + b) / ((c : ℂ) * z + d)
        = (((a : ℂ) * z + b) * (starRingEnd ℂ) ((c : ℂ) * z + d))
            * ((Complex.normSq ((c : ℂ) * z + d))⁻¹ : ℝ) := by
      rw [division_def, Complex.inv_def]
      push_cast
      ring
    rw [← UpperHalfPlane.coe_im, hcoe, key, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      hnum, hN, mul_zero, zero_add, div_eq_mul_inv]
  rw [UpperHalfPlane.cosh_dist, hd2, him,
    div_div_two_mul_aux _ _ _ hNne hyne]
  have htr : tr g = a + d := rfl
  rw [htr]
  field_simp
  linear_combination (-4 * y ^ 2) * hdet
