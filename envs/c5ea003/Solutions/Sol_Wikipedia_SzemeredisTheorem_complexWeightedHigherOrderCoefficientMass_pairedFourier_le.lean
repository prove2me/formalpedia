-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.complexWeightedHigherOrderCoefficientMass_pairedFourier_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:13.753186+00:00
-- url     : https://prove2.me/submissions/95b4172c-c3d3-48a4-9450-6e9edc996ce5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_divisorMultiplicativePhase_le_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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





end SmoothSieveCutoff



/-- If both divisor phases lie in the closed unit ball, their paired
coefficient has norm at most three. -/
theorem norm_add_sub_mul_le_three
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖z + w - z * w‖ ≤ 3 := by
  calc
    ‖z + w - z * w‖ ≤
        ‖z + w‖ + ‖z * w‖ :=
      norm_sub_le _ _
    _ ≤ (‖z‖ + ‖w‖) + ‖z‖ * ‖w‖ := by
      rw [norm_mul]
      exact add_le_add (norm_add_le z w) le_rfl
    _ ≤ 3 := by
      nlinarith [norm_nonneg z, norm_nonneg w]

/-- Uniform norm bound for the Fourier-paired coefficient at a prime. -/
theorem norm_pairedFourierPrimeCoefficient_le_three
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (t u : ℝ) :
    ‖pairedFourierPrimeCoefficient R p t u‖ ≤ 3 := by
  exact norm_add_sub_mul_le_three
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR hp t)
    (SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
      hR hp u)



















/-! ## Complex square-error Euler-product interface -/



namespace HasComplexPrimeSquareError











end HasComplexPrimeSquareError









/-! ## CFZ specialization -/















end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Complex finite averages -/
/-! ## Exact complex inclusion--exclusion -/
/-! ## Norm bounds for the complex remainder -/
/-! ## A stable complex first-order ratio -/
/-! ## Fourier phase coefficients -/

open Wikipedia.SzemeredisTheorem in
/-- The Fourier coefficient mass is uniformly at most `4^m`. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (t u : κ → ℝ) :
    complexWeightedHigherOrderCoefficientMass
        (fun q =>
          pairedFourierPrimeCoefficient R p (t q) (u q)) ≤
      (4 : ℝ) ^ Fintype.card κ := by
  calc
    complexWeightedHigherOrderCoefficientMass
        (fun q =>
          pairedFourierPrimeCoefficient R p (t q) (u q)) ≤
        ∏ q,
          (1 +
            ‖pairedFourierPrimeCoefficient
              R p (t q) (u q)‖) :=
      complexWeightedHigherOrderCoefficientMass_le_prod_one_add_norm _
    _ ≤ ∏ _q : κ, (4 : ℝ) := by
      apply Finset.prod_le_prod
      · intro q _hq
        positivity
      · intro q _hq
        linarith [
          norm_pairedFourierPrimeCoefficient_le_three
            hR hp (t q) (u q)]
    _ = (4 : ℝ) ^ Fintype.card κ := by
      simp
