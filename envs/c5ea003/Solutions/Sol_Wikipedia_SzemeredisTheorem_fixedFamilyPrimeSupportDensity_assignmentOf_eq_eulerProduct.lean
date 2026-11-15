-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.fixedFamilyPrimeSupportDensity_assignmentOf_eq_eulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:22:29.05808+00:00
-- url     : https://prove2.me/submissions/eb47ee18-2d6d-4dfc-b2fc-a77d609878c6

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_primeFactors_pairedDivisorLcm_subset_primesLE
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mem_primeFactors_pairedDivisorLcm_iff

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











/-! ## Arbitrary finite-family intersection densities -/













@[simp]
theorem affineFamilyZeroDensity_empty
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    affineFamilyZeroDensity p forms ∅ = 1 := by
  unfold affineFamilyZeroDensity
  rw [show affineFamilyZeroProduct p forms ∅ =
      fun _x => (1 : ℝ) by
    funext x
    simp [affineFamilyZeroProduct]]
  exact mean_const (α := ι → ZMod p) 1











/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















end Wikipedia.SzemeredisTheorem

end

section





/-!
# Canonical fixed-carry divisor expansions

On a canonical CFZ carry cell the affine family is fixed before the
divisor variables are chosen.  This file reorganizes the coordinatewise
truncated, squarefree paired-divisor sum by its prime-to-form supports.

The reorganization is exact.  The corresponding unrestricted support
sum factors into the existing paired Fourier local factors, and hence into
the finite-prime-support Euler series.  The difference between these two
finite sums is recorded explicitly; it is precisely the remaining
coordinatewise-truncation splice, with no divisor-dependent affine family.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## Generic finite prime-support assignments -/











theorem primeAffineFamilyZeroDensity_of_prime
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    {p : ℕ} (hp : p.Prime) (s : Finset κ) :
    primeAffineFamilyZeroDensity forms p s = by
      letI : NeZero p := ⟨hp.ne_zero⟩
      exact (affineFamilyZeroDensity p forms s : ℂ) := by
  simp [primeAffineFamilyZeroDensity, hp]













/-! ## Exact unrestricted finite Euler factorization -/







/-! ## The exact coordinatewise-truncated support fibers -/











/-! ## Replacing the supported prime range by the CRT Euler product -/

/-- Complex-valued counterpart of `prod_primesLEAsPrimes`. -/
theorem prod_primesLEAsPrimes_complex
    (R : ℕ) (f : ℕ → ℂ) :
    (∏ p ∈ primesLEAsPrimes R, f p) =
      ∏ p ∈ Nat.primesLE R, f p := by
  classical
  unfold primesLEAsPrimes
  rw [Finset.prod_map]
  exact Finset.prod_attach _ f



/-! ## The exact truncated-to-unrestricted splice -/











/-! ## Canonical fixed-carry specialization -/











/-! ## The carry-weighted canonical endpoint -/











end Wikipedia.SzemeredisTheorem

end
/-!
# Canonical fixed-carry divisor expansions

On a canonical CFZ carry cell the affine family is fixed before the
divisor variables are chosen.  This file reorganizes the coordinatewise
truncated, squarefree paired-divisor sum by its prime-to-form supports.

The reorganization is exact.  The corresponding unrestricted support
sum factors into the existing paired Fourier local factors, and hence into
the finite-prime-support Euler series.  The difference between these two
finite sums is recorded explicitly; it is precisely the remaining
coordinatewise-truncation splice, with no divisor-dependent affine family.
-/
open Wikipedia.SzemeredisTheorem
open scoped ArithmeticFunction.Moebius BigOperators
/-! ## Generic finite prime-support assignments -/
/-! ## Exact unrestricted finite Euler factorization -/
/-! ## The exact coordinatewise-truncated support fibers -/
/-! ## Replacing the supported prime range by the CRT Euler product -/

open Wikipedia.SzemeredisTheorem in
/-- On a supported squarefree divisor family, the density product over all
primes at most `R` is exactly the CRT product over the global LCM. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (forms : κ → AffineForm ι ℤ)
    (hzR : z ∈ smoothDivisorFamilyChoices κ R)
    (hz : SquarefreePairedDivisorChoice z) :
    fixedFamilyPrimeSupportDensity forms
        (fixedFamilyPrimeSupportAssignmentOf
          (primesLEAsPrimes R) z) =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        (affineFamilyZeroDensity (p : ℕ) forms
          (pairedPrimeSupport z p) : ℂ) := by
  classical
  unfold fixedFamilyPrimeSupportDensity
    fixedFamilyPrimeSupportAssignmentOf
  calc
    (∏ p : {p // p ∈ primesLEAsPrimes R},
        primeAffineFamilyZeroDensity forms (p : ℕ)
          (pairedPrimeSupport z (p : ℕ))) =
        ∏ p ∈ primesLEAsPrimes R,
          primeAffineFamilyZeroDensity forms (p : ℕ)
            (pairedPrimeSupport z (p : ℕ)) := by
      exact
        Finset.prod_coe_sort (primesLEAsPrimes R)
          (fun p : Nat.Primes =>
            (primeAffineFamilyZeroDensity forms (p : ℕ)
              (pairedPrimeSupport z (p : ℕ)) : ℂ))
    _ = ∏ p ∈ Nat.primesLE R,
          primeAffineFamilyZeroDensity forms p
            (pairedPrimeSupport z p) := by
      exact
        prod_primesLEAsPrimes_complex R
          (fun p =>
            primeAffineFamilyZeroDensity forms p
              (pairedPrimeSupport z p))
    _ = ∏ p ∈ (pairedDivisorLcm z).primeFactors,
          primeAffineFamilyZeroDensity forms p
            (pairedPrimeSupport z p) := by
      symm
      apply Finset.prod_subset
        (SmoothSieveCutoff.primeFactors_pairedDivisorLcm_subset_primesLE
          hzR hz)
      intro p hpR hpD
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primesLE hpR
      let : NeZero p := ⟨hpPrime.ne_zero⟩
      have hsupport :
          pairedPrimeSupport z p = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hnonempty
        exact hpD
          ((mem_primeFactors_pairedDivisorLcm_iff hz p).2
            ⟨hpPrime, hnonempty⟩)
      rw [primeAffineFamilyZeroDensity_of_prime forms hpPrime,
        hsupport, affineFamilyZeroDensity_empty]
      exact Complex.ofReal_one
    _ = ∏ p : (pairedDivisorLcm z).primeFactors,
          (affineFamilyZeroDensity (p : ℕ) forms
            (pairedPrimeSupport z p) : ℂ) := by
      calc
        (∏ p ∈ (pairedDivisorLcm z).primeFactors,
            primeAffineFamilyZeroDensity forms p
              (pairedPrimeSupport z p)) =
            ∏ p : (pairedDivisorLcm z).primeFactors,
              primeAffineFamilyZeroDensity forms (p : ℕ)
                (pairedPrimeSupport z p) := by
          exact
            (Finset.prod_coe_sort
              (pairedDivisorLcm z).primeFactors
              (fun p : ℕ =>
                primeAffineFamilyZeroDensity forms p
                  (pairedPrimeSupport z p))).symm
        _ = _ := by
          apply Finset.prod_congr rfl
          intro p _hp
          have hpPrime : (p : ℕ).Prime :=
            Nat.prime_of_mem_primeFactors p.2
          let : NeZero (p : ℕ) := ⟨hpPrime.ne_zero⟩
          exact primeAffineFamilyZeroDensity_of_prime
            forms hpPrime (pairedPrimeSupport z p)
