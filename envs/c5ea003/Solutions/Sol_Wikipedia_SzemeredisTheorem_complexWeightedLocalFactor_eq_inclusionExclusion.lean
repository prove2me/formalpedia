-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.complexWeightedLocalFactor_eq_inclusionExclusion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:57.229598+00:00
-- url     : https://prove2.me/submissions/48ef7d56-0b76-41bf-a614-e6cad43f52e1

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



theorem complexMean_finset_sum
    {α κ : Type*} [Fintype α]
    (s : Finset κ) (F : κ → α → ℂ) :
    complexMean (fun x => ∑ i ∈ s, F i x) =
      ∑ i ∈ s, complexMean (F i) := by
  exact Finset.expect_sum_comm Finset.univ s
    (fun x i => F i x)

theorem complexMean_mul
    {α : Type*} [Fintype α]
    (c : ℂ) (f : α → ℂ) :
    complexMean (fun x => c * f x) =
      c * complexMean f := by
  exact (Finset.mul_expect Finset.univ f c).symm

/-- Complex averaging commutes with the canonical embedding of real-valued
functions. -/
theorem complexMean_ofReal
    {α : Type*} [Fintype α] (f : α → ℝ) :
    complexMean (fun x => (f x : ℂ)) =
      (mean f : ℂ) := by
  unfold complexMean mean
  exact (algebraMap.coe_expect
    (N := ℂ) Finset.univ f).symm

/-! ## Exact complex inclusion--exclusion -/



/-- Pointwise complex-weighted inclusion--exclusion over selected
supports. -/
theorem complexWeightedLocalAvoidanceProduct_eq_inclusionExclusion
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) (x : ι → ZMod p) :
    complexWeightedLocalAvoidanceProduct p forms a x =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
          (affineFamilyZeroProduct p forms s x : ℂ) := by
  let I : κ → ℂ :=
    fun q =>
      a q *
        (finsetIndicator ((forms q).zeroFinsetZMod p) x : ℂ)
  have h :=
    Finset.prod_sub (fun _q : κ => (1 : ℂ)) I
      (Finset.univ : Finset κ)
  simpa [complexWeightedLocalAvoidanceProduct,
    affineFamilyZeroProduct, I, Finset.prod_mul_distrib,
    mul_assoc] using h











/-! ## Norm bounds for the complex remainder -/













/-! ## A stable complex first-order ratio -/









/-! ## Fourier phase coefficients -/

namespace SmoothSieveCutoff





end SmoothSieveCutoff

























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

open Wikipedia.SzemeredisTheorem in
/-- Exact complex inclusion--exclusion formula for the averaged local
factor. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p forms a =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
          (affineFamilyZeroDensity p forms s : ℂ) := by
  rw [complexWeightedLocalFactor,
    show complexWeightedLocalAvoidanceProduct p forms a =
        fun x =>
          ∑ s ∈ (Finset.univ : Finset κ).powerset,
            ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
              (affineFamilyZeroProduct p forms s x : ℂ) by
      funext x
      exact
        complexWeightedLocalAvoidanceProduct_eq_inclusionExclusion
          p forms a x]
  calc
    complexMean (fun x =>
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroProduct p forms s x : ℂ)) =
        ∑ s ∈ (Finset.univ : Finset κ).powerset,
          complexMean (fun x =>
            ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
              (affineFamilyZeroProduct p forms s x : ℂ)) :=
      complexMean_finset_sum
        (Finset.univ : Finset κ).powerset
        (fun s x =>
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroProduct p forms s x : ℂ))
    _ = ∑ s ∈ (Finset.univ : Finset κ).powerset,
          ((-1 : ℂ) ^ s.card * ∏ q ∈ s, a q) *
            (affineFamilyZeroDensity p forms s : ℂ) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [complexMean_mul, complexMean_ofReal]
      rfl
