-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
-- name    : Wikipedia.SzemeredisTheorem.abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:43.786362+00:00
-- url     : https://prove2.me/theorems/c78d5b67-3d61-43a2-b1f4-d5d76e184d9e
-- title:
--   A carry-cell cyclic contribution is close to its affine Euler product
-- statement:
--   Let $N\ne0$, fix a finite indexed CFZ family with decidable equality, natural $W,b$, an integer carry vector, and squarefree paired divisors with nonzero global LCM $D\le N$. The absolute difference between the cyclic carry-cell contribution and its cell density times the product over primes dividing $D$ of the corresponding carry-adjusted affine zero densities is at most the canonical carry-cell boundary error for $D$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryEulerBridge.lean#L603-L643

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

theorem
    Wikipedia.SzemeredisTheorem.abs_canonicalCarryCell_cyclicContribution_sub_density_mul_eulerProduct_le
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
        (N := N) (pairedDivisorLcm z) forms := by sorry
