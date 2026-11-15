-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_pairedFourierLocalFactor_sub_firstOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.177404+00:00
-- url     : https://prove2.me/submissions/05940b15-c525-44bd-b75a-0590adfdaa04

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedHigherOrderCoefficientMass_pairedFourier_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedLocalFactor_eq_firstOrder_add_remainder
import Theorems.Thm_Wikipedia_SzemeredisTheorem_minor_natAbs_le_exceptionalPrimeBound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_complexWeightedLocalFactorRemainder_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Explicit exceptional moduli for integer affine forms

The local-factor argument needs a finite bound after which every selected
nonzero coefficient and every selected nonzero two-by-two minor remains
nonzero modulo `p`.  We use a deliberately coarse sum of absolute values;
its advantage is that it is total, explicit, and requires no choices.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm



end AffineForm

theorem intCast_zmod_ne_zero_of_natAbs_lt
    {p : ℕ} {z : ℤ} (hz : z ≠ 0)
    (hzp : Int.natAbs z < p) :
    (z : ZMod p) ≠ 0 := by
  intro hzero
  have hpdivInt : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzero
  have hpdiv : p ∣ Int.natAbs z := by
    simpa using
      (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := z)).2 hpdivInt
  have hzpos : 0 < Int.natAbs z :=
    (Int.natAbs_pos.mpr hz)
  have hple : p ≤ Int.natAbs z :=
    Nat.le_of_dvd hzpos hpdiv
  omega







/-- Failure of proportionality produces a nonzero coefficient minor. -/
theorem exists_coefficientMinor_ne_zero
    {ι : Type*} {ψ φ : AffineForm ι ℤ}
    (h : ¬IntCoefficientProportional
      ψ.coefficient φ.coefficient) :
    ∃ i j, ψ.coefficientMinor φ i j ≠ 0 := by
  by_contra hzero
  push Not at hzero
  apply h
  intro i j
  exact sub_eq_zero.mp (hzero i j)



/-- Beyond the explicit bound, every minor witnessing pairwise
independence remains nonzero modulo `p`. -/
theorem exists_minor_cast_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : exceptionalPrimeBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    ∃ i j : ι,
      (((forms q).coefficientMinor (forms r) i j : ℤ) :
        ZMod p) ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    exists_coefficientMinor_ne_zero (hforms hqr)
  refine ⟨i, j, intCast_zmod_ne_zero_of_natAbs_lt hij ?_⟩
  exact (minor_natAbs_le_exceptionalPrimeBound forms q r i j).trans_lt hp

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Rank-two affine densities at good primes

For a finite system of affine forms, failure of rank two modulo `p` is
detected by the vanishing of every two-by-two coefficient minor for some
distinct pair.  This file isolates a finite, explicit exceptional set using
the sum of the absolute values of all such minors.

Outside that set, pairwise independent integer coefficient vectors remain
rank two modulo `p`.  Thus every selected subfamily containing two distinct
indices has common-zero density at most `1 / p²`: its common-zero set is
contained in the common-zero set of one rank-two pair.  This is the actual
higher-order density estimate needed for the CFZ family.  Repeated indices do
not create rank, so the hypotheses use a `Finset` and explicitly require it
to be nontrivial.

The final results instantiate
`HasGoodPrimeHigherOrderDensityEstimate` for the CFZ forms and package the
estimate together with the exact local-factor inclusion--exclusion formula.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## An explicit finite exceptional set for rank two -/















/-- The older all-purpose exceptional bound also implies the exact
rank-two good-prime condition. -/
theorem affineRankTwoGoodPrime_of_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    AffineRankTwoGoodPrime p forms := by
  refine ⟨hp, ?_⟩
  intro q r hqr
  exact exists_minor_cast_ne_zero_of_bound
    hforms hlarge hqr



/-! ## Selected-family rank and density -/

















/-! ## CFZ specialization -/



















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











/-- Quantitative complex first-order expansion at a good prime. -/
theorem norm_complexWeightedLocalFactor_sub_firstOrder_le
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p]
    (hgood : AffineRankTwoGoodPrime p forms)
    (hlarge : exceptionalPrimeBound forms < p)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactor p forms a -
        (1 - (∑ q, a q) / (p : ℂ))‖ ≤
      complexWeightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [complexWeightedLocalFactor_eq_firstOrder_add_remainder
    hnonzero hgood.1 hlarge]
  simpa using norm_complexWeightedLocalFactorRemainder_le hgood a

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
/-! ## Norm bounds for the complex remainder -/
/-! ## A stable complex first-order ratio -/
/-! ## Fourier phase coefficients -/

open Wikipedia.SzemeredisTheorem in
/-- Explicit good-prime `O_m(p⁻²)` remainder before division by the
first-order model. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R p : ℕ} [NeZero p] (hR : 2 ≤ R) (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p forms t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      (4 : ℝ) ^ Fintype.card κ /
        (p : ℝ) ^ 2 := by
  have hgood :=
    affineRankTwoGoodPrime_of_exceptionalPrimeBound
      hindependent hp hlarge
  have hbase :=
    norm_complexWeightedLocalFactor_sub_firstOrder_le
      hnonzero hgood hlarge
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
  simpa [pairedFourierLocalFactor,
    pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel, div_eq_mul_inv] using
    hbase.trans
      (mul_le_mul_of_nonneg_right
        (complexWeightedHigherOrderCoefficientMass_pairedFourier_le
          hR hp t u)
        (by positivity))
