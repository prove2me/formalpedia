-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.smoothDivisorFamilyLcmMass_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:42:20.106208+00:00
-- url     : https://prove2.me/submissions/18800d31-8475-4507-a64a-88797f5d0e19

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_abs_smoothDivisorFamilyCoefficient_le_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisorLcm_le_pow

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Uniform bounds for finite smooth-divisor expansions

The finite Selberg expansion contains two smooth Möbius-cutoff coefficients
for every form.  This file records the elementary bounds needed to propagate
a uniform arithmetic-density error through that expansion.

For a `SmoothSieveCutoff`, every cutoff value lies in `[0,1]` and the
Möbius function has absolute value at most one.  Hence each divisor summand
and each product-family coefficient has absolute value at most one.

The choice set is also counted exactly.  There are `R` positive choices in
`[1,R]`, two choices per form, and therefore

`card (smoothDivisorFamilyChoices κ R) = R ^ (2 * card κ)`.

The final theorems combine these facts with the triangle inequality.  A
uniform density perturbation of size `ε` changes the divisor sum by at most
`R ^ (2 * card κ) * ε`; a second theorem retains exactly the two scalar
prefactors occurring in the normalized Selberg expansion.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## Coefficient bounds -/





end SmoothSieveCutoff

/-! ## Exact cardinalities of the bounded choice sets -/

@[simp]
theorem card_smoothDivisorChoices (R : ℕ) :
    (smoothDivisorChoices R).card = R := by
  simp [smoothDivisorChoices]

@[simp]
theorem card_smoothDivisorPairChoices (R : ℕ) :
    (smoothDivisorPairChoices R).card = R ^ 2 := by
  simp [smoothDivisorPairChoices, pow_two]

/-- There are exactly `R ^ (2 * card κ)` paired divisor families. -/
@[simp]
theorem card_smoothDivisorFamilyChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    (smoothDivisorFamilyChoices κ R).card =
      R ^ (2 * Fintype.card κ) := by
  rw [smoothDivisorFamilyChoices, Fintype.card_piFinset]
  simp only [card_smoothDivisorPairChoices, Finset.prod_const,
    Finset.card_univ]
  rw [← pow_mul]

/-! ## Generic finite weighted perturbations -/



namespace SmoothSieveCutoff





end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# Summing the CFZ carry-block error through the divisor expansion

For a selected CFZ family with `m` forms, every smooth paired-divisor choice
has global LCM

`D ≤ R ^ (2 * m)`.

Consequently the hypothesis `R ^ (2 * m) ≤ N` makes the carry-block Euler
comparison available for every supported term.  A term with nonsquarefree
divisors has zero Möbius coefficient, so it disappears before the
squarefree CRT theorem is invoked.

This file first retains the sharp finite error mass

`∑ z, |coefficient z| * pairedDivisorLcm z`.

Discarding the coefficient and bounding both the number of choices and every
LCM by `R ^ (2 * m)` gives the explicit, deliberately crude loss

`C_{k,m} * R ^ (4 * m) / N`.

The block Euler product is kept inside the average over quotient blocks.
No common Euler product across carry blocks is asserted.
-/
open Wikipedia.SzemeredisTheorem
open scoped ArithmeticFunction.Moebius BigOperators
/-! ## LCM mass of the finite divisor expansion -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- The weighted LCM mass is bounded by the square of the uniform LCM
bound.  One factor counts divisor choices and the other bounds each LCM. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ) :
    smoothDivisorFamilyLcmMass
        (κ := κ) χ.toFun R ≤
      (R ^ (2 * Fintype.card κ) : ℝ) *
        (R ^ (2 * Fintype.card κ) : ℝ) := by
  classical
  unfold smoothDivisorFamilyLcmMass
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          (pairedDivisorLcm z : ℝ)) ≤
        ∑ _z ∈ smoothDivisorFamilyChoices κ R,
          (R ^ (2 * Fintype.card κ) : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      calc
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
              (pairedDivisorLcm z : ℝ) ≤
            1 * (R ^ (2 * Fintype.card κ) : ℝ) := by
          apply mul_le_mul
          · exact
              χ.abs_smoothDivisorFamilyCoefficient_le_one R z
          · exact_mod_cast pairedDivisorLcm_le_pow hz
          · positivity
          · norm_num
        _ = (R ^ (2 * Fintype.card κ) : ℝ) := one_mul _
    _ =
        (R ^ (2 * Fintype.card κ) : ℝ) *
          (R ^ (2 * Fintype.card κ) : ℝ) := by
      simp
