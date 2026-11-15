-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_pairedDivisibilityDensity_cfz_sub_canonicalCarryEulerAverage_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:02:25.785103+00:00
-- url     : https://prove2.me/submissions/3e7b9b39-776f-49fd-a4a6-69b2488dff5d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_cfzCanonicalCarryCellCyclicContribution_eq_density

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
/-!
# Fixed-family Euler products on canonical CFZ carry cells

The canonical carry vector is chosen before the paired divisor variables.
On one of its fibers, every cyclic CFZ value is represented by one fixed
carry-adjusted affine family.  This file defines its residue model, proves
periodicity and the exact CRT Euler product, and inserts it into the
canonical-cell discrepancy theorem.

Unlike the quotient-block Euler average, the affine family in this file
does not depend on the divisor LCM.  This is the structural feature needed
to compare the coordinatewise-truncated divisor expansion with one
unrestricted prime-support Euler series.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A fixed family attached to one canonical carry vector -/
/-! ## Periodicity -/
/-! ## Agreement with the cyclic value on one canonical cell -/
/-! ## Exact residue mean and CRT product -/
/-! ## Per-cell cyclic-to-Euler comparison -/
/-! ## Summing the canonical carry cells -/

open Wikipedia.SzemeredisTheorem in
/-- Global cyclic-to-fixed-family Euler bridge.  The error is the number of
possible carry vectors times the per-cell boundary error. -/
theorem
    solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDle : pairedDivisorLcm z ≤ N) :
    |pairedDivisibilityDensity
          (fun q (x : CubePoint k N) =>
            cfzWTrickedLinearValue W b (forms q) x)
          z -
        cfzCanonicalCarryEulerAverage
          (N := N) W b forms z| ≤
      ((cfzCanonicalCarryVectorChoices κ k).card : ℝ) *
        cfzCanonicalCarryCellBoundaryError
          (N := N) (pairedDivisorLcm z) forms := by
  rw [← sum_cfzCanonicalCarryCellCyclicContribution_eq_density
    (N := N) W b forms z]
  unfold cfzCanonicalCarryEulerAverage
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellCyclicContribution
            (N := N) W b forms carry z -
          cfzCanonicalCarryCellDensity
              (N := N) forms carry *
            ∏ p : (pairedDivisorLcm z).primeFactors,
              affineFamilyZeroDensity (p : ℕ)
                (cfzCarryAdjustedFamilyAtVector
                  N W b forms carry)
                (pairedPrimeSupport z p))| ≤
        ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          |cfzCanonicalCarryCellCyclicContribution
              (N := N) W b forms carry z -
            cfzCanonicalCarryCellDensity
                (N := N) forms carry *
              ∏ p : (pairedDivisorLcm z).primeFactors,
                affineFamilyZeroDensity (p : ℕ)
                  (cfzCarryAdjustedFamilyAtVector
                    N W b forms carry)
                  (pairedPrimeSupport z p)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _carry ∈ cfzCanonicalCarryVectorChoices κ k,
          cfzCanonicalCarryCellBoundaryError
            (N := N) (pairedDivisorLcm z) forms := by
      apply Finset.sum_le_sum
      intro carry _hcarry
      exact
        abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
          (N := N) W b forms carry z hz hDle
    _ = ((cfzCanonicalCarryVectorChoices κ k).card : ℝ) *
          cfzCanonicalCarryCellBoundaryError
            (N := N) (pairedDivisorLcm z) forms := by
      simp
