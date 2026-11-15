-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.pairedCutoffFourierEnvelope_mul_fixedFamilyPairedPrimeStateTerm
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.642486+00:00
-- url     : https://prove2.me/submissions/2081c9c8-765d-4fc1-b3a0-a1fac0e3fa71

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fixedFamilyPairedPrimeStateTerm_eq_sideProducts

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











































/-- The cutoff phase is additive-to-multiplicative in its logarithmic
variable. -/
theorem cutoffMultiplicativePhase_add
    (x y t : ℝ) :
    cutoffMultiplicativePhase (x + y) t =
      cutoffMultiplicativePhase x t *
        cutoffMultiplicativePhase y t := by
  rw [cutoffMultiplicativePhase, cutoffMultiplicativePhase,
    cutoffMultiplicativePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring







/-- The name `divisorMultiplicativePhase` is justified literally: it is
multiplicative in positive natural-number arguments. -/
theorem divisorMultiplicativePhase_mul
    (R : ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (t : ℝ) :
    divisorMultiplicativePhase R (d * e) t =
      divisorMultiplicativePhase R d t *
        divisorMultiplicativePhase R e t := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have he0 : (e : ℝ) ≠ 0 := by positivity
  rw [divisorMultiplicativePhase, divisorMultiplicativePhase,
    divisorMultiplicativePhase, Nat.cast_mul, Real.log_mul hd0 he0,
    add_div]
  exact cutoffMultiplicativePhase_add _ _ _









end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

theorem divisorMultiplicativePhase_finsetProd
    {α : Type*}
    (R : ℕ) (s : Finset α) (d : α → ℕ)
    (hd : ∀ a ∈ s, 0 < d a) (t : ℝ) :
    divisorMultiplicativePhase R (∏ a ∈ s, d a) t =
      ∏ a ∈ s, divisorMultiplicativePhase R (d a) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [divisorMultiplicativePhase, cutoffMultiplicativePhase]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [divisorMultiplicativePhase_mul]
      · rw [ih]
        intro b hb
        exact hd b (Finset.mem_insert_of_mem hb)
      · exact hd a (Finset.mem_insert_self a s)
      · exact Finset.prod_pos fun b hb =>
          hd b (Finset.mem_insert_of_mem hb)

theorem moebius_finsetProd_primes
    {α : Type*}
    (s : Finset α) (p : α → ℕ)
    (hp : ∀ a ∈ s, (p a).Prime)
    (hinj : Set.InjOn p s) :
    (ArithmeticFunction.moebius (∏ a ∈ s, p a) : ℂ) =
      (-1 : ℂ) ^ s.card := by
  classical
  have hsquare :
      Squarefree (∏ a ∈ s, p a) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro a ha b hb hab
      change IsRelPrime (p a) (p b)
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hp a ha) (hp b hb)).mpr
        (fun hpab => hab (hinj ha hb hpab))
    · intro a ha
      exact (hp a ha).squarefree
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsquare]
  push_cast
  congr 1
  have hprod :
      ArithmeticFunction.cardFactors (∏ a ∈ s, p a) =
        ∑ a ∈ s, ArithmeticFunction.cardFactors (p a) := by
    simpa using
      ArithmeticFunction.cardFactors_multiset_prod
        (s := s.1.map p)
        (by
          rw [show (s.1.map p).prod = ∏ a ∈ s, p a by simp]
          exact Finset.prod_ne_zero_iff.mpr fun a ha =>
            (hp a ha).ne_zero)
  rw [hprod]
  calc
    (∑ a ∈ s, ArithmeticFunction.cardFactors (p a)) =
        ∑ _a ∈ s, 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact ArithmeticFunction.cardFactors_apply_prime (hp a ha)
    _ = s.card := by simp

end SmoothSieveCutoff

/-! ## The three paired states at every active prime/form incidence -/













/-! ## The squarefree divisor family encoded by a state assignment -/



















theorem moebius_fixedFamilyPairedPrimeStateDivisorFamily_left
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    (ArithmeticFunction.moebius
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 : ℂ) =
      (-1 : ℂ) ^
        (fixedFamilyPairedPrimeStateLeftPrimes support A q).card := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  apply SmoothSieveCutoff.moebius_finsetProd_primes
  · intro p _hp
    exact p.1.prop
  · intro p _hp r _hr hpr
    apply Subtype.ext
    apply Subtype.ext
    exact hpr

theorem moebius_fixedFamilyPairedPrimeStateDivisorFamily_right
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    (ArithmeticFunction.moebius
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 : ℂ) =
      (-1 : ℂ) ^
        (fixedFamilyPairedPrimeStateRightPrimes support A q).card := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  apply SmoothSieveCutoff.moebius_finsetProd_primes
  · intro p _hp
    exact p.1.prop
  · intro p _hp r _hr hpr
    apply Subtype.ext
    apply Subtype.ext
    exact hpr

theorem divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_left
    {κ : Type*} [Fintype κ]
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (t : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 t =
      ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
        SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  exact SmoothSieveCutoff.divisorMultiplicativePhase_finsetProd
    R
    (fixedFamilyPairedPrimeStateLeftPrimes support A q)
    (fun p => (p : ℕ))
    (fun p _hp => p.1.prop.pos)
    t

theorem divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_right
    {κ : Type*} [Fintype κ]
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (u : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 u =
      ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
        SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) u := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  exact SmoothSieveCutoff.divisorMultiplicativePhase_finsetProd
    R
    (fixedFamilyPairedPrimeStateRightPrimes support A q)
    (fun p => (p : ℕ))
    (fun p _hp => p.1.prop.pos)
    u







































/-! ## Fourier integration of one support fiber -/

















end Wikipedia.SzemeredisTheorem

end
/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators
/-! ## The three paired states at every active prime/form incidence -/
/-! ## The squarefree divisor family encoded by a state assignment -/

open Wikipedia.SzemeredisTheorem in
/-- Each state summand, after restoring the common Fourier envelope, is
literally the transformed paired-divisor family encoded by that state
assignment. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    pairedCutoffFourierEnvelope χ t u *
        fixedFamilyPairedPrimeStateTerm R t u support A =
      χ.transformedPairedDivisorFamily R
        (fixedFamilyPairedPrimeStateDivisorFamily support A) (t, u) := by
  classical
  rw [fixedFamilyPairedPrimeStateTerm_eq_sideProducts]
  unfold pairedCutoffFourierEnvelope
    SmoothSieveCutoff.transformedPairedDivisorFamily
    SmoothSieveCutoff.transformedDivisorFamilySide
  simp_rw [
    moebius_fixedFamilyPairedPrimeStateDivisorFamily_left,
    moebius_fixedFamilyPairedPrimeStateDivisorFamily_right,
    divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_left,
    divisorMultiplicativePhase_fixedFamilyPairedPrimeStateDivisorFamily_right]
  calc
    ((∏ q, χ.cutoffFourierTransform (t q)) *
          ∏ q, χ.cutoffFourierTransform (u q)) *
        ((∏ q,
            (-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateLeftPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q)) *
          ∏ q,
            (-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateRightPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q)) =
        ((∏ q, χ.cutoffFourierTransform (t q)) *
          ∏ q,
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateLeftPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q))) *
        ((∏ q, χ.cutoffFourierTransform (u q)) *
          ∏ q,
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateRightPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q))) := by
      ring
    _ =
        (∏ q,
          χ.cutoffFourierTransform (t q) *
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateLeftPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q))) *
        ∏ q,
          χ.cutoffFourierTransform (u q) *
            ((-1 : ℂ) ^
                (fixedFamilyPairedPrimeStateRightPrimes
                  support A q).card *
              ∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
                SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q)) := by
      congr 1 <;>
        exact (Finset.prod_mul_distrib).symm
    _ = _ := by
      congr 1 <;>
        apply Finset.prod_congr rfl <;>
        intro q _hq <;>
        ring
