-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.fixedFamilyPairedPrimeStateDivisorFamily_assignmentOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:16:29.204117+00:00
-- url     : https://prove2.me/submissions/fb840247-3ddb-40bb-9383-734c043e9c6c

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mem_primesLEAsPrimes_iff

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Squarefree divisor choices -/

















/-! ## Exact prime support and the squarefree indicator product -/



@[simp]
theorem mem_pairedPrimeSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (p : ℕ) (q : κ) :
    q ∈ pairedPrimeSupport z p ↔ p ∣ pairedLocalModulus z q := by
  simp [pairedPrimeSupport]







/-! ## Arbitrary finite-family intersection densities -/

























/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















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



































theorem fixedFamilyPairedPrimeStateAssignmentOf_ne_one_iff
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (z : κ → ℕ × ℕ)
    (p : {p // p ∈ P}) (q : {q // q ∈ support p}) :
    fixedFamilyPairedPrimeStateAssignmentOf support z p q ≠ 1 ↔
      (p : ℕ) ∣ (z q).1 := by
  classical
  unfold fixedFamilyPairedPrimeStateAssignmentOf
  by_cases hleft : (p : ℕ) ∣ (z q).1 <;>
    by_cases hright : (p : ℕ) ∣ (z q).2 <;>
    simp [hleft, hright]

theorem fixedFamilyPairedPrimeStateAssignmentOf_ne_zero_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (z : κ → ℕ × ℕ)
    (hSupport :
      fixedFamilyPrimeSupportAssignmentOf P z = support)
    (p : {p // p ∈ P}) (q : {q // q ∈ support p}) :
    fixedFamilyPairedPrimeStateAssignmentOf support z p q ≠ 0 ↔
      (p : ℕ) ∣ (z q).2 := by
  have hactive :
      (p : ℕ) ∣ Nat.lcm (z q).1 (z q).2 := by
    have hmem : q.1 ∈
        fixedFamilyPrimeSupportAssignmentOf P z p := by
      rw [hSupport]
      exact q.2
    simpa [fixedFamilyPrimeSupportAssignmentOf,
      mem_pairedPrimeSupport, pairedLocalModulus] using hmem
  have hor :
      (p : ℕ) ∣ (z q).1 ∨ (p : ℕ) ∣ (z q).2 :=
    p.1.prop.dvd_lcm.mp hactive
  unfold fixedFamilyPairedPrimeStateAssignmentOf
  by_cases hleft : (p : ℕ) ∣ (z q).1
  · by_cases hright : (p : ℕ) ∣ (z q).2 <;>
      simp [hleft, hright]
  · have hright : (p : ℕ) ∣ (z q).2 := hor.resolve_left hleft
    simp [hleft, hright]



















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
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ}
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R))
    (z : κ → ℕ × ℕ)
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hzSquarefree : SquarefreePairedDivisorChoice z)
    (hSupport :
      fixedFamilyPrimeSupportAssignmentOf
          (primesLEAsPrimes R) z =
        support) :
    fixedFamilyPairedPrimeStateDivisorFamily support
        (fixedFamilyPairedPrimeStateAssignmentOf support z) =
      z := by
  funext q
  apply Prod.ext
  · let A :=
      fixedFamilyPairedPrimeStateAssignmentOf support z
    let s :=
      fixedFamilyPairedPrimeStateLeftPrimes support A q
    let e :=
      fixedFamilyPrimeSubtypeNatEmbedding (primesLEAsPrimes R)
    have hzq := Fintype.mem_piFinset.mp hzR q
    have hleftMem :=
      (Finset.mem_product.mp hzq).1
    have hleftPos : 0 < (z q).1 :=
      (Finset.mem_Icc.mp hleftMem).1
    have hleftLe : (z q).1 ≤ R :=
      (Finset.mem_Icc.mp hleftMem).2
    have hmap :
        s.map e = (z q).1.primeFactors := by
      ext r
      constructor
      · intro hr
        obtain ⟨p, hpS, hpr⟩ := Finset.mem_map.mp hr
        have hpDiv :
            (p : ℕ) ∣ (z q).1 := by
          rw [mem_fixedFamilyPairedPrimeStateLeftPrimes] at hpS
          obtain ⟨hq, hstate⟩ := hpS
          exact
            (fixedFamilyPairedPrimeStateAssignmentOf_ne_one_iff
              support z p ⟨q, hq⟩).mp
              (by simpa using hstate)
        have hrPrime : r.Prime := by
          rw [← hpr]
          exact p.1.prop
        have hrDiv : r ∣ (z q).1 := by
          rw [← hpr]
          exact hpDiv
        exact Nat.mem_primeFactors.mpr
          ⟨hrPrime, hrDiv, hleftPos.ne'⟩
      · intro hr
        have hrData := Nat.mem_primeFactors.mp hr
        have hrPrime : r.Prime := hrData.1
        have hrDiv : r ∣ (z q).1 := hrData.2.1
        have hrLe : r ≤ R :=
          (Nat.le_of_dvd hleftPos hrDiv).trans hleftLe
        let rp : Nat.Primes := ⟨r, hrPrime⟩
        have hrpMem : rp ∈ primesLEAsPrimes R :=
          (mem_primesLEAsPrimes_iff R rp).2 hrLe
        let p : {p // p ∈ primesLEAsPrimes R} := ⟨rp, hrpMem⟩
        have hpSupport :
            q ∈ support p := by
          rw [← hSupport]
          rw [fixedFamilyPrimeSupportAssignmentOf,
            mem_pairedPrimeSupport, pairedLocalModulus,
            p.1.prop.dvd_lcm]
          exact Or.inl (by simpa [p, rp] using hrDiv)
        have hpState :
            A p ⟨q, hpSupport⟩ ≠ 1 := by
          exact
            (fixedFamilyPairedPrimeStateAssignmentOf_ne_one_iff
              support z p ⟨q, hpSupport⟩).2
              (by simpa [p, rp] using hrDiv)
        have hpS : p ∈ s := by
          exact
            (mem_fixedFamilyPairedPrimeStateLeftPrimes
              support A q p).2 ⟨hpSupport, hpState⟩
        exact Finset.mem_map.mpr
          ⟨p, hpS, rfl⟩
    unfold fixedFamilyPairedPrimeStateDivisorFamily
    calc
      (∏ p ∈ s, (p : ℕ)) =
          ∏ r ∈ s.map e, r := by
        symm
        exact Finset.prod_map s e (fun r : ℕ => r)
      _ = ∏ r ∈ (z q).1.primeFactors, r := by
        rw [hmap]
      _ = (z q).1 :=
        Nat.prod_primeFactors_of_squarefree (hzSquarefree q).1
  · let A :=
      fixedFamilyPairedPrimeStateAssignmentOf support z
    let s :=
      fixedFamilyPairedPrimeStateRightPrimes support A q
    let e :=
      fixedFamilyPrimeSubtypeNatEmbedding (primesLEAsPrimes R)
    have hzq := Fintype.mem_piFinset.mp hzR q
    have hrightMem :=
      (Finset.mem_product.mp hzq).2
    have hrightPos : 0 < (z q).2 :=
      (Finset.mem_Icc.mp hrightMem).1
    have hrightLe : (z q).2 ≤ R :=
      (Finset.mem_Icc.mp hrightMem).2
    have hmap :
        s.map e = (z q).2.primeFactors := by
      ext r
      constructor
      · intro hr
        obtain ⟨p, hpS, hpr⟩ := Finset.mem_map.mp hr
        have hpSupport :
            q ∈ support p := by
          have hpSel :
              p ∈ fixedFamilyPairedPrimeStateRightPrimes
                support A q := hpS
          rw [mem_fixedFamilyPairedPrimeStateRightPrimes] at hpSel
          exact hpSel.choose
        have hpState :
            A p ⟨q, hpSupport⟩ ≠ 0 := by
          have hpSel :
              p ∈ fixedFamilyPairedPrimeStateRightPrimes
                support A q := hpS
          rw [mem_fixedFamilyPairedPrimeStateRightPrimes] at hpSel
          simpa using hpSel.choose_spec
        have hpDiv :
            (p : ℕ) ∣ (z q).2 :=
          (fixedFamilyPairedPrimeStateAssignmentOf_ne_zero_iff
            support z hSupport p ⟨q, hpSupport⟩).mp hpState
        have hrPrime : r.Prime := by
          rw [← hpr]
          exact p.1.prop
        have hrDiv : r ∣ (z q).2 := by
          rw [← hpr]
          exact hpDiv
        exact Nat.mem_primeFactors.mpr
          ⟨hrPrime, hrDiv, hrightPos.ne'⟩
      · intro hr
        have hrData := Nat.mem_primeFactors.mp hr
        have hrPrime : r.Prime := hrData.1
        have hrDiv : r ∣ (z q).2 := hrData.2.1
        have hrLe : r ≤ R :=
          (Nat.le_of_dvd hrightPos hrDiv).trans hrightLe
        let rp : Nat.Primes := ⟨r, hrPrime⟩
        have hrpMem : rp ∈ primesLEAsPrimes R :=
          (mem_primesLEAsPrimes_iff R rp).2 hrLe
        let p : {p // p ∈ primesLEAsPrimes R} := ⟨rp, hrpMem⟩
        have hpSupport :
            q ∈ support p := by
          rw [← hSupport]
          rw [fixedFamilyPrimeSupportAssignmentOf,
            mem_pairedPrimeSupport, pairedLocalModulus,
            p.1.prop.dvd_lcm]
          exact Or.inr (by simpa [p, rp] using hrDiv)
        have hpState :
            A p ⟨q, hpSupport⟩ ≠ 0 :=
          (fixedFamilyPairedPrimeStateAssignmentOf_ne_zero_iff
            support z hSupport p ⟨q, hpSupport⟩).2
            (by simpa [p, rp] using hrDiv)
        have hpS : p ∈ s :=
          (mem_fixedFamilyPairedPrimeStateRightPrimes
            support A q p).2 ⟨hpSupport, hpState⟩
        exact Finset.mem_map.mpr
          ⟨p, hpS, rfl⟩
    unfold fixedFamilyPairedPrimeStateDivisorFamily
    calc
      (∏ p ∈ s, (p : ℕ)) =
          ∏ r ∈ s.map e, r := by
        symm
        exact Finset.prod_map s e (fun r : ℕ => r)
      _ = ∏ r ∈ (z q).2.primeFactors, r := by
        rw [hmap]
      _ = (z q).2 :=
        Nat.prod_primeFactors_of_squarefree (hzSquarefree q).2
