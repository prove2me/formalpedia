-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.fixedFamilyPairedPrimeStateTerm_eq_sideProducts
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:52:34.685343+00:00
-- url     : https://prove2.me/submissions/75ae1b27-9456-44d5-928a-bfbd221386c7

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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





end SmoothSieveCutoff

/-! ## The three paired states at every active prime/form incidence -/













/-! ## The squarefree divisor family encoded by a state assignment -/





@[simp]
theorem mem_fixedFamilyPairedPrimeStateLeftPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  classical
  simp [fixedFamilyPairedPrimeStateLeftPrimes]

@[simp]
theorem mem_fixedFamilyPairedPrimeStateRightPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  classical
  simp [fixedFamilyPairedPrimeStateRightPrimes]



theorem pairedFourierPrimeStateTerm_eq_side_mul
    (R p : ℕ) (t u : ℝ) (state : Fin 3) :
    pairedFourierPrimeStateTerm R p t u state =
      (if state ≠ 1 then
          -SmoothSieveCutoff.divisorMultiplicativePhase R p t
        else 1) *
      (if state ≠ 0 then
          -SmoothSieveCutoff.divisorMultiplicativePhase R p u
        else 1) := by
  fin_cases state <;>
    simp [pairedFourierPrimeStateTerm]

theorem fintype_prod_prod_mul
    {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    {M : Type*} [CommMonoid M]
    (f g : ∀ i, α i → M) :
    (∏ i, ∏ a, f i a * g i a) =
      (∏ i, ∏ a, f i a) * ∏ i, ∏ a, g i a := by
  simp_rw [Finset.prod_mul_distrib]

theorem fintype_prod_subtype_eq_prod_dite
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ∀ i, i ∈ s → M) :
    (∏ i : {i // i ∈ s}, f i i.2) =
      ∏ i : ι, if hi : i ∈ s then f i hi else 1 := by
  classical
  let g : ι → M := fun i =>
    if hi : i ∈ s then f i hi else 1
  calc
    (∏ i : {i // i ∈ s}, f i i.2) =
        ∏ i : {i // i ∈ s}, g i := by
      apply Finset.prod_congr rfl
      intro i _hi
      simp [g, i.2]
    _ = ∏ i ∈ s, g i :=
      Finset.prod_coe_sort s g
    _ = ∏ i : ι, g i := by
      symm
      calc
        (∏ i : ι, g i) =
            ∏ i : ι, if i ∈ s then g i else 1 := by
          apply Finset.prod_congr rfl
          intro i _hi
          by_cases hi : i ∈ s <;> simp [g, hi]
        _ = ∏ i ∈ s, g i :=
          Fintype.prod_ite_mem s g
    _ = _ := rfl

















































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
/-- The state product can be regrouped by form and by side. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    fixedFamilyPairedPrimeStateTerm R t u support A =
      (∏ q : κ,
          ((-1 : ℂ) ^
              (fixedFamilyPairedPrimeStateLeftPrimes
                support A q).card *
            (∏ p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q,
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q)))) *
        (∏ q : κ,
          ((-1 : ℂ) ^
              (fixedFamilyPairedPrimeStateRightPrimes
                support A q).card *
            (∏ p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q,
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q)))) := by
  classical
  unfold fixedFamilyPairedPrimeStateTerm
  simp_rw [pairedFourierPrimeStateTerm_eq_side_mul]
  rw [fintype_prod_prod_mul]
  congr 1
  · calc
      (∏ p : {p // p ∈ P},
          ∏ q : {q // q ∈ support p},
            if A p q ≠ 1 then
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q)
            else 1) =
          ∏ p : {p // p ∈ P},
            ∏ q : κ,
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 1 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (t q)
                else 1
              else 1 := by
        apply Finset.prod_congr rfl
        intro p _hp
        exact
          fintype_prod_subtype_eq_prod_dite
            (support p)
            (fun q hq =>
              if A p ⟨q, hq⟩ ≠ 1 then
                -SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (t q)
              else 1)
      _ =
          ∏ q : κ,
            ∏ p : {p // p ∈ P},
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 1 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (t q)
                else 1
              else 1 := by
        rw [Finset.prod_comm]
      _ =
          ∏ q : κ,
            ∏ p ∈
                fixedFamilyPairedPrimeStateLeftPrimes support A q,
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q) := by
        apply Finset.prod_congr rfl
        intro q _hq
        conv_rhs =>
          rw [← Fintype.prod_ite_mem]
        apply Finset.prod_congr rfl
        intro p _hp
        by_cases hmem :
            p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q
        · obtain ⟨hqp, hstate⟩ :=
            (mem_fixedFamilyPairedPrimeStateLeftPrimes
              support A q p).mp hmem
          simp [hqp, hstate, hmem]
        · have hnot :
              ¬∃ hqp : q ∈ support p, A p ⟨q, hqp⟩ ≠ 1 := by
            simpa using hmem
          by_cases hqp : q ∈ support p
          · have hstate : A p ⟨q, hqp⟩ = 1 := by
              by_contra hne
              exact hnot ⟨hqp, hne⟩
            simp [hqp, hstate, hmem]
          · simp [hqp, hmem]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q _hq
        rw [Finset.prod_neg]
  · calc
      (∏ p : {p // p ∈ P},
          ∏ q : {q // q ∈ support p},
            if A p q ≠ 0 then
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q)
            else 1) =
          ∏ p : {p // p ∈ P},
            ∏ q : κ,
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 0 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (u q)
                else 1
              else 1 := by
        apply Finset.prod_congr rfl
        intro p _hp
        exact
          fintype_prod_subtype_eq_prod_dite
            (support p)
            (fun q hq =>
              if A p ⟨q, hq⟩ ≠ 0 then
                -SmoothSieveCutoff.divisorMultiplicativePhase
                  R (p : ℕ) (u q)
              else 1)
      _ =
          ∏ q : κ,
            ∏ p : {p // p ∈ P},
              if hq : q ∈ support p then
                if A p ⟨q, hq⟩ ≠ 0 then
                  -SmoothSieveCutoff.divisorMultiplicativePhase
                    R (p : ℕ) (u q)
                else 1
              else 1 := by
        rw [Finset.prod_comm]
      _ =
          ∏ q : κ,
            ∏ p ∈
                fixedFamilyPairedPrimeStateRightPrimes support A q,
              -SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q) := by
        apply Finset.prod_congr rfl
        intro q _hq
        conv_rhs =>
          rw [← Fintype.prod_ite_mem]
        apply Finset.prod_congr rfl
        intro p _hp
        by_cases hmem :
            p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q
        · obtain ⟨hqp, hstate⟩ :=
            (mem_fixedFamilyPairedPrimeStateRightPrimes
              support A q p).mp hmem
          simp [hqp, hstate, hmem]
        · have hnot :
              ¬∃ hqp : q ∈ support p, A p ⟨q, hqp⟩ ≠ 0 := by
            simpa using hmem
          by_cases hqp : q ∈ support p
          · have hstate : A p ⟨q, hqp⟩ = 0 := by
              by_contra hne
              exact hnot ⟨hqp, hne⟩
            simp [hqp, hstate, hmem]
          · simp [hqp, hmem]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q _hq
        rw [Finset.prod_neg]
