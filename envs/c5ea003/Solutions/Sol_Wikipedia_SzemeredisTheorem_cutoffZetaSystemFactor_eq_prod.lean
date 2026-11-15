-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutoffZetaSystemFactor_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:08.159463+00:00
-- url     : https://prove2.me/submissions/1e15759b-0d52-426f-8213-0d9c6578528b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaShift_add_ne_zero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/

/-
The completion definitions and their differentiability proofs below are
backported from Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean at
 db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
section GreenTaoZetaCompatibility

open Set Filter Complex
open scoped Topology











lemma riemannZeta_eq_inv_sub_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := by grind [riemannZeta₁, riemannZeta₀]





end GreenTaoZetaCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology





/-- Away from zero, the completed factor is the usual residue-normalized
zeta function. -/
theorem zetaResidueFactor_eq_mul_riemannZeta
    {z : ℂ} (hz : z ≠ 0) :
    zetaResidueFactor z = z * riemannZeta (1 + z) := by
  have hs : (1 : ℂ) + z ≠ 1 := by
    intro h
    apply hz
    exact add_left_cancel (by simpa only [add_zero] using h)
  rw [riemannZeta_eq_inv_sub_mul hs]
  simp [zetaResidueFactor, hz]























/-- Raw zeta form of one completed pair factor.  The hypotheses are exactly
the nonvanishing conditions needed to divide by the uncompleted factors. -/
theorem normalizedZetaPairFactor_eq
    {u v : ℂ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0)
    (hζu : riemannZeta (1 + u) ≠ 0)
    (hζv : riemannZeta (1 + v) ≠ 0) :
    normalizedZetaPairFactor u v =
      ((u + v) / (u * v)) *
        (riemannZeta (1 + u + v) /
          (riemannZeta (1 + u) *
            riemannZeta (1 + v))) := by
  rw [normalizedZetaPairFactor,
    zetaResidueFactor_eq_mul_riemannZeta huv,
    zetaResidueFactor_eq_mul_riemannZeta hu,
    zetaResidueFactor_eq_mul_riemannZeta hv]
  field_simp
  ring_nf

/-! ## Finite systems of paired zeta factors -/











/-- Exact raw-zeta expression for a finite system of paired parameters. -/
theorem normalizedZetaSystemFactor_eq_prod
    {κ : Type*} [Fintype κ]
    {u v : κ → ℂ}
    (hu : ∀ i, u i ≠ 0)
    (hv : ∀ i, v i ≠ 0)
    (huv : ∀ i, u i + v i ≠ 0)
    (hζu : ∀ i, riemannZeta (1 + u i) ≠ 0)
    (hζv : ∀ i, riemannZeta (1 + v i) ≠ 0) :
    normalizedZetaSystemFactor u v =
      ∏ i,
        (((u i + v i) / (u i * v i)) *
          (riemannZeta (1 + u i + v i) /
            (riemannZeta (1 + u i) *
              riemannZeta (1 + v i)))) := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedZetaPairFactor_eq
    (hu i) (hv i) (huv i) (hζu i) (hζv i)

end Wikipedia.SzemeredisTheorem

end

section





/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology



theorem cutoffZetaShift_re
    (R : ℕ) (t : ℝ) :
    (cutoffZetaShift R t).re =
      1 / Real.log R := by
  change
    (Complex.ofReal ((Real.log (R : ℝ))⁻¹) *
      ((1 : ℂ) -
        Complex.ofReal (2 * Real.pi * t) *
          Complex.I)).re =
      1 / Real.log R
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.one_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero]
  rw [one_div]
  simp

theorem cutoffZetaShift_re_pos
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    0 < (cutoffZetaShift R t).re := by
  rw [cutoffZetaShift_re R]
  exact one_div_pos.mpr
    (Real.log_pos (by exact_mod_cast hR))

theorem cutoffZetaShift_ne_zero
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    cutoffZetaShift R t ≠ 0 := by
  intro hzero
  have hre := cutoffZetaShift_re_pos hR t
  rw [hzero] at hre
  norm_num at hre









/-- Every shifted zeta argument lies in the classical half-plane of
absolute convergence. -/
theorem one_lt_one_add_cutoffZetaShift_re
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    1 < (1 + cutoffZetaShift R t).re := by
  rw [Complex.add_re, Complex.one_re]
  exact lt_add_of_pos_right 1
    (cutoffZetaShift_re_pos hR t)

/-- Zeta is nonzero at every Fourier shift, using its absolutely convergent
half-plane rather than a separate zero-free-region argument. -/
theorem riemannZeta_one_add_cutoffZetaShift_ne_zero
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    riemannZeta (1 + cutoffZetaShift R t) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re
    (one_lt_one_add_cutoffZetaShift_re hR t)

/-! ## Finite Fourier systems -/









/-! ## The standard growing truncation box -/







end Wikipedia.SzemeredisTheorem

end
/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## Finite Fourier systems -/

open Wikipedia.SzemeredisTheorem in
/-- Exact raw-zeta product for all paired Fourier parameters.  Positivity of
the real parts discharges every denominator nonvanishing condition. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSystemFactor R t u =
      ∏ i,
        (((cutoffZetaShift R (t i) +
              cutoffZetaShift R (u i)) /
            (cutoffZetaShift R (t i) *
              cutoffZetaShift R (u i))) *
          (riemannZeta
                (1 + cutoffZetaShift R (t i) +
                  cutoffZetaShift R (u i)) /
            (riemannZeta
                  (1 + cutoffZetaShift R (t i)) *
              riemannZeta
                  (1 + cutoffZetaShift R (u i))))) := by
  rw [cutoffZetaSystemFactor]
  exact normalizedZetaSystemFactor_eq_prod
    (fun i => cutoffZetaShift_ne_zero hR (t i))
    (fun i => cutoffZetaShift_ne_zero hR (u i))
    (fun i => cutoffZetaShift_add_ne_zero hR (t i) (u i))
    (fun i =>
      riemannZeta_one_add_cutoffZetaShift_ne_zero
        hR (t i))
    (fun i =>
      riemannZeta_one_add_cutoffZetaShift_ne_zero
        hR (u i))
