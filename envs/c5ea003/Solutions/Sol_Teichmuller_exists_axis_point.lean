-- Prove2me | solution 1 for Teichmuller.exists_axis_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:00:55.370218+00:00
-- url     : https://prove2.me/submissions/c0ae9171-f708-455a-ac64-2499278100e0

-- Sol generated from Geometry/Teichmuller/TranslationLength.lean
import Mathlib
import Definitions.Def_Geometry_Teichmuller_TorusSpace
import Definitions.Def_Geometry_Teichmuller_TranslationLength
import Theorems.Thm_Teichmuller_cosh_dist_smul
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
theorem solution(g : SL(2, R)) (ht : 2 < |tr g|) :
    ∃ z : ℍ, Real.cosh (dist z (g • z)) = (tr g ^ 2 - 2) / 2 := by
  set a := entry g 0 0 with ha
  set b := entry g 0 1 with hb
  set c := entry g 1 0 with hc
  set d := entry g 1 1 with hd
  have hdet : a * d - b * c = 1 := entry_det g
  have htr : tr g = a + d := rfl
  have ht4 : 4 < (a + d) ^ 2 := by
    rw [htr] at ht
    nlinarith [abs_nonneg (a + d), sq_abs (a + d), le_abs_self (a + d), neg_abs_le (a + d)]
  have hdisc : (a - d) ^ 2 + 4 * (b * c) = (a + d) ^ 2 - 4 := by linarith [hdet]
  rcases eq_or_ne c 0 with hc0 | hc0
  · -- upper triangular case: the axis is a vertical line
    have hadd : (a - d) ^ 2 = (a + d) ^ 2 - 4 := by rw [← hdisc, hc0]; ring
    have hne : a - d ≠ 0 := by
      intro h
      rw [h] at hadd
      nlinarith
    refine ⟨⟨⟨-b / (a - d), 1⟩, by norm_num⟩, ?_⟩
    rw [cosh_dist_smul, htr]
    have hre : (⟨(⟨-b / (a - d), 1⟩ : ℂ), by norm_num⟩ : ℍ).re = -b / (a - d) := rfl
    have him : (⟨(⟨-b / (a - d), 1⟩ : ℂ), by norm_num⟩ : ℍ).im = 1 := rfl
    rw [hre, him, ← hc, hc0, ← ha, ← hb, ← hd]
    field_simp
    ring
  · -- generic case: the axis is a semicircle
    have hpos : (0:ℝ) < ((a + d) ^ 2 - 4) / (4 * c ^ 2) := by
      have : (0:ℝ) < 4 * c ^ 2 := by positivity
      have h4 : (0:ℝ) < (a + d) ^ 2 - 4 := by linarith
      positivity
    set y0 := Real.sqrt (((a + d) ^ 2 - 4) / (4 * c ^ 2)) with hy0
    have hy0pos : 0 < y0 := Real.sqrt_pos.mpr hpos
    have hy0sq : y0 ^ 2 = ((a + d) ^ 2 - 4) / (4 * c ^ 2) := Real.sq_sqrt hpos.le
    refine ⟨⟨⟨(a - d) / (2 * c), y0⟩, hy0pos⟩, ?_⟩
    rw [cosh_dist_smul, htr]
    have hre : (⟨(⟨(a - d) / (2 * c), y0⟩ : ℂ), hy0pos⟩ : ℍ).re = (a - d) / (2 * c) := rfl
    have him : (⟨(⟨(a - d) / (2 * c), y0⟩ : ℂ), hy0pos⟩ : ℍ).im = y0 := rfl
    rw [hre, him, ← hc, hy0sq]
    have hEzero : c * (((a - d) / (2 * c)) ^ 2 + ((a + d) ^ 2 - 4) / (4 * c ^ 2))
        - (a - d) * ((a - d) / (2 * c)) - b = 0 := by
      field_simp
      linarith [hdisc]
    have hy0ne : y0 ≠ 0 := hy0pos.ne'
    rw [hEzero]
    simp
