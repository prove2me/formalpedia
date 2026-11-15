-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_pairedFourierLocalFactor_sub_firstOrder_le_of_goodPrime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.192513+00:00
-- url     : https://prove2.me/submissions/2b847021-ea80-440f-a45a-0050a624f094

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedHigherOrderCoefficientMass_pairedFourier_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedLocalFactor_eq_firstOrder_add_remainder_of_goodPrime
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_complexWeightedLocalFactorRemainder_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Modular one-form geometry -/









/-! ## Scaling identities and W-trick preservation -/

















/-! ## Exact one- and two-form densities -/









/-! ## Complex first-order expansion from modular geometry -/



/-- Complex local-factor remainder bound using only direct modular
one- and two-form geometry. -/
theorem norm_complexWeightedLocalFactor_sub_firstOrder_le_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (a : κ → ℂ) :
    ‖complexWeightedLocalFactor p forms a -
        (1 - (∑ q, a q) / (p : ℂ))‖ ≤
      complexWeightedHigherOrderCoefficientMass a *
        ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [
    complexWeightedLocalFactor_eq_firstOrder_add_remainder_of_goodPrime
      hnonzero]
  simpa using
    norm_complexWeightedLocalFactorRemainder_le hrankTwo a

/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/

























end Wikipedia.SzemeredisTheorem

end
/-!
# Uniform Euler tails on CFZ carry blocks

The carry-block reduction leaves a genuinely varying affine system.  The
paired divisor choice determines the block side length, the point of the
quotient block determines all carry constants, and all of these data may
vary with the asymptotic parameter.  This file keeps that dependence.

At a prime outside the primorial, carry corrections alter only affine
constants.  The direct modular one-form and rank-two predicates therefore
give the same `O_k(p⁻²)` arithmetic-to-zeta ratio estimate on every block,
uniformly in the divisor choice and in both Fourier variables.  The general
dominated Euler-product theorem then shows that the product over `p > w`
tends to one as `w → ∞`.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open scoped BigOperators
/-! ## A dependent package for a varying carry block -/
/-! ## Direct modular local estimate -/

open Wikipedia.SzemeredisTheorem in
/-- A direct-good-prime arithmetic local factor differs from the common
first-order model by `O(4^m p⁻²)`.  Unlike the natural-constant W-trick
specialization, this statement permits arbitrary integer affine constants. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hR : 2 ≤ R) (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p forms t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      (4 : ℝ) ^ Fintype.card κ / (p : ℝ) ^ 2 := by
  have hbase :=
    norm_complexWeightedLocalFactor_sub_firstOrder_le_of_goodPrime
      hnonzero hrankTwo
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
  simpa [pairedFourierLocalFactor,
    pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel, div_eq_mul_inv] using
    hbase.trans
      (mul_le_mul_of_nonneg_right
        (complexWeightedHigherOrderCoefficientMass_pairedFourier_le
          hR hnonzero.1 t u)
        (by positivity))
