-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.boxMean_cfzCanonicalCarryIndicator_mul_eq_cellSum_div
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:36.324205+00:00
-- url     : https://prove2.me/submissions/a104f25d-d6ea-45de-905f-0e58cf27fed1

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section







/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## LCM bounds -/









/-! ## Finite boxes -/















/-- `boxSum` is the usual sum over the literal finset `natBox`. -/
theorem boxSum_eq_sum_natBox {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) :
    boxSum side F = ∑ x ∈ natBox side, F x := by
  rw [← Finset.sum_coe_sort]
  exact Fintype.sum_equiv (finiteBoxEquivNatBox side)
    (fun x : FiniteBox side ↦ F (fun i ↦ x i))
    (fun x : ↥(natBox side) ↦ F x)
    (fun _ ↦ rfl)

/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/































end Wikipedia.SzemeredisTheorem

end

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
/-- Masking by the carry indicator is the same as summing over the
corresponding canonical carry finset. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ) :
    boxMean (fun _ : CFZVariable k => N)
        (fun x =>
          cfzCanonicalCarryIndicator
              (N := N) forms carry x *
            F x) =
      (∑ x ∈ cfzCanonicalCarryCell
          (N := N) forms carry, F x) /
        ∏ _v : CFZVariable k, (N : ℝ) := by
  rw [boxMean, boxSum_eq_sum_natBox]
  unfold cfzCanonicalCarryCell
    cfzCanonicalCarryIndicator
  simp only [Finset.sum_filter]
  apply congrArg (fun r : ℝ => r / ∏ _v : CFZVariable k, (N : ℝ))
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry
  · simp [hcarry]
  · simp [hcarry]
