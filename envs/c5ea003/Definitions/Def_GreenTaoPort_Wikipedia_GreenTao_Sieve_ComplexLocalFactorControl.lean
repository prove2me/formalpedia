-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:03:12.656765+00:00
-- url     : https://prove2.me/theorems/9c73dd47-0545-424b-a6cb-bf8bae5f7faf
-- title:
--   Complex affine local factors and prime-square error control
-- statement:
--   For finite index and coordinate types with decidable equality and a nonzero modulus $p$, the complex local factor is the normalized mean of $\prod_q(1-a_q1_{\{\psi_q=0\}})$ over affine inputs modulo $p$. Its higher-order remainder sums the contributions of supports of cardinality at least two; the associated coefficient mass sums the products of $\|a_q\|$ on those supports. The first-order model is $1-(\sum_q a_q)/p$.
--
--   For paired Fourier phases, the coefficient for one form is $z+w-zw$, giving paired arithmetic factors and first-order models. The predicate $\operatorname{HasComplexPrimeSquareError}(C,a)$ requires $C\ge0$ and $\|a_p-1\|\le C/p^2$ at every prime. A bounded-mask construction replaces factors at primes at most a chosen natural cutoff by $1$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ComplexLocalFactorControl.lean#L43-L842

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Lean
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The normalized average of a complex-valued function on a finite type. -/
noncomputable def complexMean
    {α : Type*} [Fintype α] (f : α → ℂ) : ℂ :=
  𝔼 x, f x







/-! ## Exact complex inclusion--exclusion -/

/-- The pointwise local avoidance product with arbitrary complex
coefficients. -/
noncomputable def complexWeightedLocalAvoidanceProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) (x : ι → ZMod p) : ℂ :=
  ∏ q, (1 -
    a q *
      (finsetIndicator ((forms q).zeroFinsetZMod p) x : ℂ))



/-- The complex arithmetic local factor, defined as the normalized
finite-field average of the pointwise avoidance product. -/
noncomputable def complexWeightedLocalFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) : ℂ :=
  complexMean (complexWeightedLocalAvoidanceProduct p forms a)





/-- The signed complex contribution of supports of cardinality at least
two. -/
noncomputable def complexWeightedLocalFactorRemainder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) : ℂ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
      (affineFamilyZeroDensity p forms s : ℂ)



/-! ## Norm bounds for the complex remainder -/

/-- Total norm mass carried by supports of cardinality at least two. -/
noncomputable def complexWeightedHigherOrderCoefficientMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ → ℂ) : ℝ :=
  ∑ s ∈ higherOrderSelectedSupports κ,
    ∏ q ∈ s, ‖a q‖











/-! ## A stable complex first-order ratio -/

/-- The first-order local model belonging to a complex coefficient
family. -/
noncomputable def complexFirstOrderLocalModel
    {κ : Type*} [Fintype κ] (p : ℕ) (a : κ → ℂ) : ℂ :=
  1 - (∑ q, a q) / (p : ℂ)







/-! ## Fourier phase coefficients -/

namespace SmoothSieveCutoff





end SmoothSieveCutoff

/-- The coefficient of the prime-zero indicator obtained from the two
squarefree divisor choices attached to one form. -/
noncomputable def pairedFourierPrimeCoefficient
    (R p : ℕ) (t u : ℝ) : ℂ :=
  SmoothSieveCutoff.divisorMultiplicativePhase R p t +
    SmoothSieveCutoff.divisorMultiplicativePhase R p u -
      SmoothSieveCutoff.divisorMultiplicativePhase R p t *
        SmoothSieveCutoff.divisorMultiplicativePhase R p u





/-- The arithmetic local factor after assigning two Fourier parameters to
each affine form. -/
noncomputable def pairedFourierLocalFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) : ℂ :=
  complexWeightedLocalFactor p forms
    (fun q => pairedFourierPrimeCoefficient R p (t q) (u q))

/-- Its matching first-order complex model. -/
noncomputable def pairedFourierFirstOrderLocalModel
    {κ : Type*} [Fintype κ]
    (R p : ℕ) (t u : κ → ℝ) : ℂ :=
  complexFirstOrderLocalModel p
    (fun q => pairedFourierPrimeCoefficient R p (t q) (u q))















/-! ## Complex square-error Euler-product interface -/

/-- Uniform square-decay control for complex local factors. -/
def HasComplexPrimeSquareError
    (C : ℝ) (localFactor : Nat.Primes → ℂ) : Prop :=
  0 ≤ C ∧
    ∀ p, ‖localFactor p - 1‖ ≤ C / (p : ℝ) ^ 2

namespace HasComplexPrimeSquareError











end HasComplexPrimeSquareError

/-- Replace every complex local factor below a numerical cutoff by one. -/
def boundedMaskedComplexPrimeLocalFactor
    (B : ℕ) (localFactor : Nat.Primes → ℂ) :
    Nat.Primes → ℂ :=
  fun p => if (p : ℕ) ≤ B then 1 else localFactor p







/-! ## CFZ specialization -/















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.boundedMaskedComplexPrimeLocalFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.complexFirstOrderLocalModel.eq_1,
    `Wikipedia.SzemeredisTheorem.complexWeightedHigherOrderCoefficientMass.congr_simp,
    `Wikipedia.SzemeredisTheorem.complexWeightedLocalAvoidanceProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.complexWeightedLocalFactor.congr_simp,
    `Wikipedia.SzemeredisTheorem.complexWeightedLocalFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.complexWeightedLocalFactorRemainder.congr_simp,
    `Wikipedia.SzemeredisTheorem.pairedFourierFirstOrderLocalModel.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedFourierLocalFactor.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


