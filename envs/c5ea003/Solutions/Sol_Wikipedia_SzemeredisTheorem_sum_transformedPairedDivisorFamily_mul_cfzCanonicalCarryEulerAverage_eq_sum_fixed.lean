-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_transformedPairedDivisorFamily_mul_cfzCanonicalCarryEulerAverage_eq_sum_fixed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:47:18.038998+00:00
-- url     : https://prove2.me/submissions/cc84bc9f-6113-4b37-af0f-8234596dcc67

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm











@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl









end Wikipedia.SzemeredisTheorem

end

section




/-!
# Small-prime local factors for W-tricked affine forms

If `ψ` is an integer affine form, the affine form occurring after the
`W`-trick is

`x ↦ W * ψ(x) + b`.

At a prime `p ∣ W` this form is identically `b` modulo `p`.  When `b` is a
reduced residue modulo `W`, it is therefore nowhere zero modulo `p`.  This
makes every small-prime avoidance factor, including the complex factor
produced by paired Fourier inversion, exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem wTrickedAffineForm_constant {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).constant =
      (W : ℤ) * ψ.constant + b :=
  rfl

@[simp]
theorem wTrickedAffineForm_coefficient {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) (i : ι) :
    (wTrickedAffineForm W b ψ).coefficient i =
      (W : ℤ) * ψ.coefficient i :=
  rfl



























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

























/-! ## Exact unrestricted finite Euler factorization -/







/-! ## The exact coordinatewise-truncated support fibers -/











/-! ## Replacing the supported prime range by the CRT Euler product -/





/-! ## The exact truncated-to-unrestricted splice -/











/-! ## Canonical fixed-carry specialization -/











/-! ## The carry-weighted canonical endpoint -/





/-- Complex coercion of the canonical carry Euler average, expressed as
the weighted sum of the fixed-family products used in this file. -/
theorem coe_cfzCanonicalCarryEulerAverage_eq_sum_fixed
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) :
    (cfzCanonicalCarryEulerAverage
        (N := N) W b forms z : ℂ) =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellDensity
            (N := N) forms carry : ℂ) *
          cfzCanonicalCarryFixedDivisorEulerProduct
            N W b forms carry z := by
  unfold cfzCanonicalCarryEulerAverage
    cfzCanonicalCarryFixedDivisorEulerProduct
    fixedFamilyDivisorEulerProduct
  push_cast
  rfl





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
/-! ## The exact truncated-to-unrestricted splice -/
/-! ## Canonical fixed-carry specialization -/
/-! ## The carry-weighted canonical endpoint -/

open Wikipedia.SzemeredisTheorem in
/-- Reordering the two finite sums identifies the divisor expansion
weighted by `cfzCanonicalCarryEulerAverage` with the carrywise fixed-family
expansions. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (W b R : ℕ)
    (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          (cfzCanonicalCarryEulerAverage
            (N := N) W b forms z : ℂ) =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellDensity
            (N := N) forms carry : ℂ) *
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            χ.transformedPairedDivisorFamily R z (t, u) *
              cfzCanonicalCarryFixedDivisorEulerProduct
                N W b forms carry z := by
  classical
  simp_rw [coe_cfzCanonicalCarryEulerAverage_eq_sum_fixed]
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
            (cfzCanonicalCarryCellDensity
                (N := N) forms carry : ℂ) *
              cfzCanonicalCarryFixedDivisorEulerProduct
                N W b forms carry z) =
        ∑ z ∈ smoothDivisorFamilyChoices κ R,
          ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
            χ.transformedPairedDivisorFamily R z (t, u) *
              ((cfzCanonicalCarryCellDensity
                  (N := N) forms carry : ℂ) *
                cfzCanonicalCarryFixedDivisorEulerProduct
                  N W b forms carry z) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.mul_sum]
    _ = ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          ∑ z ∈ smoothDivisorFamilyChoices κ R,
            χ.transformedPairedDivisorFamily R z (t, u) *
              ((cfzCanonicalCarryCellDensity
                  (N := N) forms carry : ℂ) *
                cfzCanonicalCarryFixedDivisorEulerProduct
                  N W b forms carry z) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro carry _hcarry
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      ring
