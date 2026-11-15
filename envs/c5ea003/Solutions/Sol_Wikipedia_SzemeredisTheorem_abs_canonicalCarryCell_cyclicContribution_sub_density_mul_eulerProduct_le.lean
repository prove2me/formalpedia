-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:00:31.40754+00:00
-- url     : https://prove2.me/submissions/e3c6f683-f222-4624-97e0-bcec1ff990bf

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_canonicalCarryCell_residueContribution_sub_density_mul_residueDensity_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisibilityHasAffinePrimeModels_affineFormResidueValue
import Theorems.Thm_Wikipedia_SzemeredisTheorem_pairedDivisibilityIndicator_cfz_eq_carryVectorResidue_of_eq

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
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic natural representative for an affine residue -/







/-- Exact squarefree CRT factorization for the natural representatives of
an arbitrary finite affine family. -/
theorem pairedDivisibilityDensity_affineFormResidueValue_eq_prod
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ) [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisibilityDensity
        (fun q =>
          affineFormResidueValue
            (D := pairedDivisorLcm z) (forms q)) z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ) forms
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_eq_prod_affineFamilyZeroDensity
      z
      (fun q =>
        affineFormResidueValue
          (D := pairedDivisorLcm z) (forms q))
      forms hz
      (pairedDivisibilityHasAffinePrimeModels_affineFormResidueValue
        forms z hz)

/-! ## Complete quotient blocks and their affine families -/









/-! ## Good complete quotient blocks -/













/-! ## Exact blockwise CRT and averaged Euler products -/







/-! ## The complete-block mean is the averaged Euler product -/



/-! ## The outer partial-block boundary -/







/-! ## Unconditional cyclic-to-Euler approximation -/









/-! ## Selected-family specialization -/









/-! ## Carry-dependent constants and primes dividing `W` -/



















/-! ## Good primes outside `W` -/



















end Wikipedia.SzemeredisTheorem

end

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A fixed family attached to one canonical carry vector -/







/-! ## Periodicity -/





/-! ## Agreement with the cyclic value on one canonical cell -/





/-- Multiplication by the canonical-cell indicator makes the cyclic and
fixed-family residue models equal on the whole natural box. -/
theorem
    cfzCanonicalCarryIndicator_mul_pairedDivisibilityIndicator_eq_residue
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (x : CFZVariable k → ℕ) :
    cfzCanonicalCarryIndicator (N := N) forms carry x *
        pairedDivisibilityIndicator
          (fun q y =>
            cfzWTrickedLinearValue W b (forms q)
              (cubePointOfNat (N := N) y))
          z x =
      cfzCanonicalCarryIndicator (N := N) forms carry x *
        pairedDivisibilityIndicator
          (fun q y =>
            cfzCarryAdjustedResidueValueAtVector
              (D := pairedDivisorLcm z)
              N W b forms carry q
              (fun v =>
                (y v : ZMod (pairedDivisorLcm z))))
          z x := by
  by_cases hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry
  · rw [pairedDivisibilityIndicator_cfz_eq_carryVectorResidue_of_eq
      W b forms carry z x hcarry]
  · simp [cfzCanonicalCarryIndicator, hcarry]

/-! ## Exact residue mean and CRT product -/



/-- For a squarefree paired divisor choice, the preceding density is the
exact CRT Euler product of the fixed carry-adjusted affine family. -/
theorem pairedDivisibilityDensity_cfzCarryVector_eq_eulerProduct
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z) :
    pairedDivisibilityDensity
        (fun q =>
          cfzCarryAdjustedResidueValueAtVector
            (D := pairedDivisorLcm z)
            N W b forms carry q)
        z =
      ∏ p : (pairedDivisorLcm z).primeFactors,
        affineFamilyZeroDensity (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N W b forms carry)
          (pairedPrimeSupport z p) := by
  exact
    pairedDivisibilityDensity_affineFormResidueValue_eq_prod
      (cfzCarryAdjustedFamilyAtVector
        N W b forms carry) z hz

/-! ## Per-cell cyclic-to-Euler comparison -/



















/-- The cyclic and fixed residue contributions agree exactly after masking
by the canonical-cell indicator. -/
theorem cfzCanonicalCarryCellCyclicContribution_eq_residueContribution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)] :
    cfzCanonicalCarryCellCyclicContribution
        (N := N) W b forms carry z =
      cfzCanonicalCarryCellResidueContribution
        (N := N) W b forms carry z := by
  unfold cfzCanonicalCarryCellCyclicContribution
    cfzCanonicalCarryCellResidueContribution
    cfzCarryVectorResiduePairedIndicator
  apply congrArg
    (boxMean (fun _ : CFZVariable k => N))
  funext x
  exact
    cfzCanonicalCarryIndicator_mul_pairedDivisibilityIndicator_eq_residue
      W b forms carry z x



/-- The contribution of one canonical carry cell is its box density times
the exact finite residue density, up to the explicit boundary error. -/
theorem
    abs_canonicalCarryCell_cyclicContribution_sub_density_mul_residueDensity_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hDle : pairedDivisorLcm z ≤ N) :
    |cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z -
        cfzCanonicalCarryCellDensity
            (N := N) forms carry *
          cfzCarryVectorPairedDivisibilityDensity
            N W b forms carry z| ≤
      cfzCanonicalCarryCellBoundaryError
        (N := N) (pairedDivisorLcm z) forms := by
  rw [cfzCanonicalCarryCellCyclicContribution_eq_residueContribution
    W b forms carry z]
  exact
    abs_canonicalCarryCell_residueContribution_sub_density_mul_residueDensity_le
      W b forms carry z hDle



/-! ## Summing the canonical carry cells -/









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

open Wikipedia.SzemeredisTheorem in
/-- The same comparison with the finite density rewritten as its exact CRT
Euler product. -/
theorem
    solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (z : κ → ℕ × ℕ)
    [NeZero (pairedDivisorLcm z)]
    (hz : SquarefreePairedDivisorChoice z)
    (hDle : pairedDivisorLcm z ≤ N) :
    |cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z -
        cfzCanonicalCarryCellDensity
            (N := N) forms carry *
          ∏ p : (pairedDivisorLcm z).primeFactors,
            affineFamilyZeroDensity (p : ℕ)
              (cfzCarryAdjustedFamilyAtVector
                N W b forms carry)
              (pairedPrimeSupport z p)| ≤
      cfzCanonicalCarryCellBoundaryError
        (N := N) (pairedDivisorLcm z) forms := by
  have h :=
    abs_canonicalCarryCell_cyclicContribution_sub_density_mul_residueDensity_le
      (N := N) W b forms carry z hDle
  have heuler :
      cfzCarryVectorPairedDivisibilityDensity
          N W b forms carry z =
        ∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ)
            (cfzCarryAdjustedFamilyAtVector
              N W b forms carry)
            (pairedPrimeSupport z p) := by
    unfold cfzCarryVectorPairedDivisibilityDensity
    exact
      pairedDivisibilityDensity_cfzCarryVector_eq_eulerProduct
        N W b forms carry z hz
  rw [heuler] at h
  exact h
