-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor_eq_invLog_pow_mul_prod_kernel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:13.734762+00:00
-- url     : https://prove2.me/submissions/0677543f-2de4-4ebf-bca0-ea95bd6b9413

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The cutoff zeta pole as the normalizer kernel

For the Fourier shift

`z_R(t) = (1 - 2πit) / log R`,

the elementary pole contribution in one completed zeta quotient is

`z_R(t) z_R(u) / (z_R(t) + z_R(u))`.

This file identifies it exactly with `1 / log R` times the archimedean
kernel evaluated in `CutoffNormalizerIntegral`.  The identity is then
multiplied over a finite selected family and combined with both products of
cutoff Fourier transforms.  No limit is taken here: these are exact
algebraic normalization formulas.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- The full elementary zeta pole is the product normalizer kernel times
one inverse logarithm for every selected form. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSingularFactor R t u =
      ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
          Fintype.card κ) *
        ∏ i,
          SmoothSieveCutoff.cutoffNormalizerKernel
            (t i) (u i) := by
  classical
  rw [cutoffZetaSingularFactor]
  calc
    (∏ i,
        (cutoffZetaShift R (t i) *
            cutoffZetaShift R (u i)) /
          (cutoffZetaShift R (t i) +
            cutoffZetaShift R (u i))) =
        ∏ i,
          ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
            SmoothSieveCutoff.cutoffNormalizerKernel
              (t i) (u i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
          hR (t i) (u i)
    _ =
        ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
            Fintype.card κ) *
          ∏ i,
            SmoothSieveCutoff.cutoffNormalizerKernel
              (t i) (u i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ]
