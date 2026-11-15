-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_pairedFourierPrimeCoefficient_le_three_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:22:34.666377+00:00
-- url     : https://prove2.me/submissions/79e820be-5f65-4684-9906-e3c7fe461f3b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
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
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_divisorMultiplicativePhase_le_one

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier inversion for the smooth sieve cutoff

This file supplies the analytic transform used in the Goldston--Yıldırım
calculation.  For a smooth sieve cutoff `χ`, put

`g(x) = exp(x) χ(x)`.

We regard `g` as complex-valued and use Mathlib's analyst normalization

`𝓕 g(t) = ∫ x, exp(-2 π i x t) g(x)`.

The function `g` is smooth and compactly supported, hence is a Schwartz
function.  Its Fourier transform is therefore again Schwartz and in
particular integrable.  Fourier inversion gives

`χ(x) = ∫ t, 𝓕 g(t) exp(-x + 2 π i t x)`.

At `x = log d / log R`, the last exponential is multiplicative in `d`.
The final results interchange this integral with the finite divisor sums
that occur in the truncated divisor sum.
-/

namespace Wikipedia.SzemeredisTheorem

open Function MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators FourierTransform
  ContDiff SchwartzMap

namespace SmoothSieveCutoff































@[simp]
theorem norm_inverseFourierCharacter (x t : ℝ) :
    ‖inverseFourierCharacter x t‖ = 1 := by
  rw [inverseFourierCharacter, Complex.norm_exp]
  simp









/-- The cutoff phase is the inverse Fourier character times the real
exponential `exp(-x)`. -/
theorem cutoffMultiplicativePhase_eq
    (x t : ℝ) :
    cutoffMultiplicativePhase x t =
      (Real.exp (-x) : ℂ) * inverseFourierCharacter x t := by
  simp only [cutoffMultiplicativePhase, inverseFourierCharacter,
    Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]



















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Complex good-prime local factors after Fourier inversion

Fourier inversion turns each of the two smooth divisor sums attached to a
form into a complex multiplicative phase.  At a prime `p`, if the two phases
are `z` and `w`, the four squarefree divisor choices contribute

`1 - (z + w - z * w) 1_{p ∣ ψ(x)}`.

Thus the arithmetic local factor is a complex-weighted avoidance average.
This file develops that average directly over `ℂ`, proves its exact finite
inclusion--exclusion expansion, and isolates the singleton contribution.
At a rank-two good prime the remaining supports have density at most
`p⁻²`, so the complex remainder is bounded by the product of
`1 + ‖a q‖`.

For the Fourier coefficients, every divisor phase has norm at most one when
`R ≥ 2`, hence `‖z + w - z * w‖ ≤ 3`.  Consequently the higher-order
coefficient mass is at most `4 ^ m` for a system of `m` forms.  Above
`p ≥ 6m`, the complex first-order model has norm at least `1/2`; division by
that model therefore gives the explicit ratio estimate

`‖localRatio p - 1‖ ≤ 2 * 4 ^ m / p²`.

The final CFZ theorem masks the finite exceptional range and packages these
ratios in a complex analogue of `HasPrimeSquareError`, including
multipliability of the resulting remainder Euler product.

This does not yet compare the first-order model with the local factors of
the appropriate multivariate zeta quotient.  That analytic comparison, and
the subsequent parameter-uniform integration, are separate steps.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Complex finite averages -/









/-! ## Exact complex inclusion--exclusion -/















/-! ## Norm bounds for the complex remainder -/













/-! ## A stable complex first-order ratio -/









/-! ## Fourier phase coefficients -/

namespace SmoothSieveCutoff

/-- The exact norm of the multiplicative cutoff phase. -/
theorem norm_cutoffMultiplicativePhase
    (x t : ℝ) :
    ‖cutoffMultiplicativePhase x t‖ =
      Real.exp (-x) := by
  rw [cutoffMultiplicativePhase_eq, norm_mul,
    norm_inverseFourierCharacter, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]



end SmoothSieveCutoff

























/-! ## Complex square-error Euler-product interface -/



namespace HasComplexPrimeSquareError











end HasComplexPrimeSquareError









/-! ## CFZ specialization -/















end Wikipedia.SzemeredisTheorem

end

section



/-!
# Unrestricted finite-prime-support Euler series

An Euler product is not the pointwise factorization of the divisor sum in
which every divisor is separately truncated by `d ≤ R`.  This file records
the honest unrestricted object that has such a factorization.

For a prime-indexed family `L p`, put

`E S = ∏ p ∈ S, (L p - 1)`

for a finite set of active primes `S`.  If the local errors are absolutely
summable, then the series over all finite prime supports is absolutely
summable and

`∑' S, E S = ∏' p, L p`.

Thus the unrestricted squarefree prime-support expansion has a rigorous
Euler product, with no divisor cutoff and no conditional rearrangement.
The final section specializes the construction to the exact paired Fourier
local factors.  Comparing this unrestricted series with the original
coordinatewise truncation remains a separate approximation theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Generic absolutely convergent support expansion -/













/-! ## Absolute convergence of paired-Fourier local errors -/

/-- The norm of a prime Fourier phase is an exact real power.  In
particular it is independent of the Fourier frequency. -/
theorem SmoothSieveCutoff.norm_divisorMultiplicativePhase_prime_eq_rpow
    {R : ℕ} (_hR : 1 < R)
    (p : Nat.Primes) (t : ℝ) :
    ‖divisorMultiplicativePhase R (p : ℕ) t‖ =
      (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) := by
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  rw [divisorMultiplicativePhase,
    norm_cutoffMultiplicativePhase,
    Real.rpow_def_of_pos hp0]
  congr 1
  rw [div_eq_mul_inv]
  ring









/-! ## Direct-good-prime and carry-block versions -/





namespace SelectedCFZCarryFourierBlockData











end SelectedCFZCarryFourierBlockData

/-! ## Exact paired-Fourier specialization -/





end Wikipedia.SzemeredisTheorem

end
/-!
# Unrestricted finite-prime-support Euler series

An Euler product is not the pointwise factorization of the divisor sum in
which every divisor is separately truncated by `d ≤ R`.  This file records
the honest unrestricted object that has such a factorization.

For a prime-indexed family `L p`, put

`E S = ∏ p ∈ S, (L p - 1)`

for a finite set of active primes `S`.  If the local errors are absolutely
summable, then the series over all finite prime supports is absolutely
summable and

`∑' S, E S = ∏' p, L p`.

Thus the unrestricted squarefree prime-support expansion has a rigorous
Euler product, with no divisor cutoff and no conditional rearrangement.
The final section specializes the construction to the exact paired Fourier
local factors.  Comparing this unrestricted series with the original
coordinatewise truncation remains a separate approximation theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Generic absolutely convergent support expansion -/
/-! ## Absolute convergence of paired-Fourier local errors -/

open Wikipedia.SzemeredisTheorem in
/-- The paired prime coefficient retains the power saving coming from the
positive real part of the Fourier shift. -/
theorem solution
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : ℝ) :
    ‖pairedFourierPrimeCoefficient
        R (p : ℕ) t u‖ ≤
      3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) := by
  let x : ℝ :=
    (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  have hx0 : 0 ≤ x := by
    exact (Real.rpow_pos_of_pos hp0 _).le
  have ht :
      ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t‖ = x := by
    exact
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_prime_eq_rpow
        (by omega) p t
  have hu :
      ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) u‖ = x := by
    exact
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_prime_eq_rpow
        (by omega) p u
  have hx1 : x ≤ 1 := by
    rw [← ht]
    exact
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
        hR p.prop t
  let z : ℂ :=
    SmoothSieveCutoff.divisorMultiplicativePhase
      R (p : ℕ) t
  let w : ℂ :=
    SmoothSieveCutoff.divisorMultiplicativePhase
      R (p : ℕ) u
  unfold pairedFourierPrimeCoefficient
  calc
    ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t +
        SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) u -
        SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) t *
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) u‖ ≤
        (‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) t‖ +
            ‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) u‖) +
          ‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) t‖ *
            ‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) u‖ := by
      change ‖z + w - z * w‖ ≤
        (‖z‖ + ‖w‖) + ‖z‖ * ‖w‖
      calc
        ‖z + w - z * w‖ ≤
            ‖z + w‖ + ‖z * w‖ :=
          norm_sub_le _ _
        _ = ‖z + w‖ + ‖z‖ * ‖w‖ := by
          rw [norm_mul]
        _ ≤ (‖z‖ + ‖w‖) + ‖z‖ * ‖w‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ = (x + x) + x * x := by rw [ht, hu]
    _ ≤ 3 * x := by nlinarith
