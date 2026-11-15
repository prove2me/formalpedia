-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.abs_selectedCFZ_weightedDensity_sub_canonicalEuler_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:03:45.998499+00:00
-- url     : https://prove2.me/submissions/a5ac7238-200d-44c0-abdb-b2e9ddb9f19e

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_pairedDivisibilityDensity_cfz_sub_canonicalCarryEulerAverage_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzCanonicalCarryCellBoundaryError_le_div
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisorLcm_le_pow
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisorLcm_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_squarefreePairedDivisorChoice_of_coefficient_ne_zero

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

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## LCM mass of the finite divisor expansion -/



/-- The existing LCM bound, specialized to a selected CFZ family. -/
theorem pairedDivisorLcm_selectedCFZ_le_pow
    {k R : ℕ} (e : LinearFormsExponent k)
    {z : SelectedCFZFormIndex e → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices
      (SelectedCFZFormIndex e) R) :
    pairedDivisorLcm z ≤
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) :=
  pairedDivisorLcm_le_pow hz



/-! ## The unscaled selected-family divisor sums -/





namespace SmoothSieveCutoff









/-! ## Reinsert the normalized Selberg prefactor -/







end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# Summed canonical cyclic-to-Euler boundary

The canonical carry partition compares the cyclic paired-divisibility
density with a divisor-independent affine Euler model.  Its pointwise error
is proportional to the paired-divisor LCM divided by the cyclic modulus.
This file sums that estimate over every divisor family selected by a
Boolean CFZ exponent, restores the Selberg normalization, and records a
joint power-scale limit.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- A supported selected divisor term inherits the canonical carry-cell
boundary estimate.  The global fit hypothesis supplies `2D ≤ N` uniformly
for every divisor family in the selected box. -/
theorem solution
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : z ∈ smoothDivisorFamilyChoices
      (SelectedCFZFormIndex e) R) :
    |smoothDivisorFamilyCoefficient χ.toFun R z *
          pairedDivisibilityDensity
            (fun q : SelectedCFZFormIndex e =>
              fun x : CubePoint k N =>
                cfzWTrickedLinearValue W b q.1 x)
            z -
        smoothDivisorFamilyCoefficient χ.toFun R z *
          cfzCanonicalCarryEulerAverage
            (N := N) W b
            (fun q : SelectedCFZFormIndex e => q.1) z| ≤
      |smoothDivisorFamilyCoefficient χ.toFun R z| *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
  classical
  by_cases hcoefficient :
      smoothDivisorFamilyCoefficient χ.toFun R z = 0
  · simp [hcoefficient]
  · have hDpos : 0 < pairedDivisorLcm z :=
      pairedDivisorLcm_pos hz
    let : NeZero (pairedDivisorLcm z) :=
      ⟨Nat.ne_of_gt hDpos⟩
    have hDpow :
        pairedDivisorLcm z ≤
          R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) :=
      pairedDivisorLcm_selectedCFZ_le_pow e hz
    have hDle : pairedDivisorLcm z ≤ N := by omega
    have hDfit : 2 * pairedDivisorLcm z ≤ N := by omega
    have hsquarefree : SquarefreePairedDivisorChoice z :=
      squarefreePairedDivisorChoice_of_coefficient_ne_zero
        χ.toFun R z hcoefficient
    have hcanonical :=
      abs_pairedDivisibilityDensity_cfz_sub_canonicalCarryEulerAverage_le
        (N := N) W b
        (fun q : SelectedCFZFormIndex e => q.1)
        z hsquarefree hDle
    have hboundary :=
      cfzCanonicalCarryCellBoundaryError_le_div
        (κ := SelectedCFZFormIndex e)
        hk hDpos hDfit
        (fun q : SelectedCFZFormIndex e => q.1)
    rw [← mul_sub, abs_mul]
    calc
      |smoothDivisorFamilyCoefficient χ.toFun R z| *
          |pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  fun x : CubePoint k N =>
                    cfzWTrickedLinearValue W b q.1 x)
                z -
            cfzCanonicalCarryEulerAverage
              (N := N) W b
              (fun q : SelectedCFZFormIndex e => q.1) z| ≤
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          (((cfzCanonicalCarryVectorChoices
              (SelectedCFZFormIndex e) k).card : ℝ) *
            cfzCanonicalCarryCellBoundaryError
              (N := N) (pairedDivisorLcm z)
              (fun q : SelectedCFZFormIndex e => q.1)) :=
        mul_le_mul_of_nonneg_left hcanonical (abs_nonneg _)
      _ ≤
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          (((cfzCanonicalCarryVectorChoices
              (SelectedCFZFormIndex e) k).card : ℝ) *
            ((cfzCanonicalCarryCellErrorConstant
                (SelectedCFZFormIndex e) k : ℝ) *
              (pairedDivisorLcm z : ℝ) / (N : ℝ))) := by
        gcongr
      _ =
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
        unfold selectedCFZCanonicalCyclicBoundaryConstant
        push_cast
        ring
