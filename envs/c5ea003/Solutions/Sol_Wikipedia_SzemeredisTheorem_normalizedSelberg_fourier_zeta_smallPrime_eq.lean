-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.normalizedSelberg_fourier_zeta_smallPrime_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:25:05.697795+00:00
-- url     : https://prove2.me/submissions/68f2c1fa-7ede-4e0b-9663-8cb7b82e48d1

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_fourierProducts_mul_cutoffZetaSingularFactor_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_normalizedSelbergScale_log_zeta_density_cancellation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Exact W-tricked Fourier normalization

The normalized Selberg majorant contributes, for every selected form,

`(φ(W) / W) / (cχ log R)` and `(log R)²`.

The elementary pole in the zeta quotient contributes `(log R)⁻¹`, while
the omitted primes dividing the primorial contribute the inverse
reduced-residue density.  This file records the exact cancellation:

`Selberg scale × (log R)² × zeta pole × small-prime correction`

is

`cχ⁻¹ × cutoff-normalizer kernel × normalized small-prime residual`.

The identity is pointwise in all Fourier variables.  Specializing
`cχ` to the derivative-square normalizer and replacing the two correction
factors by one leaves an integrand whose full integral is exactly one.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- **Exact pointwise normalization identity.**  This is the algebraic
core of the main term calculation, before the completed-zeta and
large-prime correction factors (which may simply be multiplied onto both
sides). -/
theorem solution
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R) (w : ℕ)
    (t u : κ → ℝ) :
    (normalizedSelbergScale χ.normalizer R (primorial w) : ℂ) ^
            Fintype.card κ *
          (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card κ *
            (χ.fourierProductTransform t *
              χ.fourierProductTransform u *
              cutoffZetaSingularFactor R t u)) *
          smallPrimeZetaCorrection R w t u =
      ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          normalizedSmallPrimeZetaCorrection R w t u := by
  rw [χ.fourierProducts_mul_cutoffZetaSingularFactor_eq
    hR t u]
  rw [normalizedSmallPrimeZetaCorrection]
  have hscalar :=
    normalizedSelbergScale_log_zeta_density_cancellation
      χ.normalizer χ.normalizer_pos.ne'
      hR w (Fintype.card κ)
  calc
    (normalizedSelbergScale χ.normalizer R (primorial w) : ℂ) ^
            Fintype.card κ *
          (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card κ *
            (((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
                Fintype.card κ) *
              χ.cutoffNormalizerSeparatedProduct (t, u))) *
          smallPrimeZetaCorrection R w t u =
        ((normalizedSelbergScale χ.normalizer R
              (primorial w) : ℂ) ^ Fintype.card κ *
            (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^
              Fintype.card κ *
              ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
                Fintype.card κ)) *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          smallPrimeZetaCorrection R w t u) := by
      ring
    _ =
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          primorialReducedResidueDensity w ^
            Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          smallPrimeZetaCorrection R w t u := by
      rw [hscalar]
    _ =
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          (primorialReducedResidueDensity w ^
            Fintype.card κ *
            smallPrimeZetaCorrection R w t u) := by
      ring
