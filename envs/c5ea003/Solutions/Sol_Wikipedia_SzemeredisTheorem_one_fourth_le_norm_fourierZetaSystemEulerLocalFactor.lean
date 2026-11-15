-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:56:47.46674+00:00
-- url     : https://prove2.me/submissions/a0a1ed5a-40b5-4741-ac11-a0cfef17fc3a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_divisorMultiplicativePhase_le_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_half_le_norm_complexFirstOrderLocalModel

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

section



/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic finite-product second-order remainder -/









/-! ## One paired phase -/















/-! ## Exact cpow coordinates -/













/-! ## Finite systems -/



























/-! ## Direct arithmetic/zeta comparison -/









theorem complexZetaModelDifferenceConstant_eq_natCast
    (m : ℕ) :
    complexZetaModelDifferenceConstant m =
      (complexZetaModelDifferenceNat m : ℝ) := by
  rw [complexZetaModelDifferenceConstant,
    complexZetaModelDifferenceNat]
  push_cast
  ring













end Wikipedia.SzemeredisTheorem

end
/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A generic finite-product second-order remainder -/
/-! ## One paired phase -/
/-! ## Exact cpow coordinates -/
/-! ## Finite systems -/
/-! ## Direct arithmetic/zeta comparison -/

open Wikipedia.SzemeredisTheorem in
/-- Above the stability cutoff, the exact finite-system zeta Euler model
has norm at least one quarter. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    (1 : ℝ) / 4 ≤
      ‖fourierZetaSystemEulerLocalFactor R p t u‖ := by
  classical
  let m := Fintype.card κ
  let model :=
    pairedFourierFirstOrderLocalModel R p t u
  have hcomparison :
      complexZetaModelComparisonCutoff m ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hcard :
      6 * m ≤ p :=
    (Nat.le_max_right 7 (6 * m)).trans
      hcomparison
  have hfirst :
      (1 : ℝ) / 2 ≤ ‖model‖ := by
    exact one_half_le_norm_complexFirstOrderLocalModel
      hp hcard
      (fun q =>
        norm_pairedFourierPrimeCoefficient_le_three
          hR hp (t q) (u q))
  have hdiff :=
    norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
      hR hp
      ((Nat.le_max_left 7 (6 * m)).trans
        hcomparison)
      t u
  have hCnat :
      4 * complexZetaModelDifferenceNat m ≤ p :=
    (Nat.le_max_right
      (complexZetaModelComparisonCutoff m)
      (4 * complexZetaModelDifferenceNat m)).trans
        hcut
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp.one_le
  have hCcast :
      4 * (complexZetaModelDifferenceNat m : ℝ) ≤
        (p : ℝ) := by
    exact_mod_cast hCnat
  have hpSq :
      (p : ℝ) ≤ (p : ℝ) ^ 2 := by
    nlinarith
  have hsmall :
      complexZetaModelDifferenceConstant m /
          (p : ℝ) ^ 2 ≤
        (1 : ℝ) / 4 := by
    rw [complexZetaModelDifferenceConstant_eq_natCast]
    rw [div_le_iff₀ (sq_pos_of_pos hpR)]
    nlinarith
  have hdiffQuarter :
      ‖fourierZetaSystemEulerLocalFactor R p t u -
          model‖ ≤ (1 : ℝ) / 4 :=
    hdiff.trans hsmall
  calc
    (1 : ℝ) / 4 ≤
        ‖model‖ -
          ‖model -
            fourierZetaSystemEulerLocalFactor R p t u‖ := by
      rw [norm_sub_rev]
      linarith
    _ ≤
        ‖model -
          (model -
            fourierZetaSystemEulerLocalFactor R p t u)‖ :=
      norm_sub_norm_le _ _
    _ =
        ‖fourierZetaSystemEulerLocalFactor R p t u‖ := by
      congr 1
      ring
