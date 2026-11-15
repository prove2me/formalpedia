-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.div_trimToMultiple_pow_le_mul_two_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:13.599991+00:00
-- url     : https://prove2.me/submissions/442c0665-cea6-4414-8bdc-86075cf3b393

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
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

















/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/





/-- Trimming never increases an interval. -/
theorem trimToMultiple_le (D L : ℕ) :
    trimToMultiple D L ≤ L :=
  Nat.div_mul_le_self L D

/-- Quotient--remainder decomposition expressed using the trimmed length. -/
theorem trimToMultiple_add_mod (D L : ℕ) :
    trimToMultiple D L + L % D = L := by
  simpa [trimToMultiple, Nat.add_comm, Nat.mul_comm] using
    Nat.mod_add_div L D

/-- The exact number of points removed by trimming `[0, L)` to a multiple of
`D` is `L % D`. -/
theorem trimToMultiple_loss (D L : ℕ) :
    L - trimToMultiple D L = L % D := by
  have h := trimToMultiple_add_mod D L
  omega

/-- Fewer than `D` points are removed from a single interval when `D > 0`. -/
theorem trimToMultiple_boundary_lt {D L : ℕ} (hD : 0 < D) :
    L - trimToMultiple D L < D := by
  rw [trimToMultiple_loss]
  exact Nat.mod_lt L hD



















end Wikipedia.SzemeredisTheorem

end

section


/-!
# Power bounds for the canonical carry-cell boundary

The canonical carry Euler bridge has an exact error with two terms:

* the outer part of the `N`-box removed when trimming to side-`D` blocks;
* the carry-transition set inside the trimmed box.

This file converts that exact expression into the standard power estimate.
Under `2 * D ≤ N`, the trimmed side is at least `N / 2`; hence its
`t`-dimensional volume loses at most a factor `2^t`.  Combining this with
the existing codimension-one carry-transition count gives an explicit
`O_{k,|κ|}(D/N)` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



/-- If at least two full block sides fit inside the ambient side, trimming
to a multiple of `D` retains at least half the side. -/
theorem le_two_mul_trimToMultiple
    {D N : ℕ} (hD : 0 < D) (hfit : 2 * D ≤ N) :
    N ≤ 2 * trimToMultiple D N := by
  have htrimle : trimToMultiple D N ≤ N :=
    trimToMultiple_le D N
  have hloss : N - trimToMultiple D N < D :=
    trimToMultiple_boundary_lt hD
  have hdecomp :
      trimToMultiple D N +
          (N - trimToMultiple D N) = N :=
    Nat.add_sub_of_le htrimle
  omega

/-- Real power form of the retained-half-volume estimate. -/
theorem pow_le_two_pow_mul_trimToMultiple_pow
    {D N t : ℕ} (hD : 0 < D) (hfit : 2 * D ≤ N) :
    (N : ℝ) ^ t ≤
      (2 : ℝ) ^ t * (trimToMultiple D N : ℝ) ^ t := by
  have hside : (N : ℝ) ≤
      2 * (trimToMultiple D N : ℝ) := by
    exact_mod_cast le_two_mul_trimToMultiple hD hfit
  calc
    (N : ℝ) ^ t ≤
        (2 * (trimToMultiple D N : ℝ)) ^ t :=
      pow_le_pow_left₀ (by positivity) hside t
    _ = (2 : ℝ) ^ t *
        (trimToMultiple D N : ℝ) ^ t := by
      rw [mul_pow]











end Wikipedia.SzemeredisTheorem

end
/-!
# Power bounds for the canonical carry-cell boundary

The canonical carry Euler bridge has an exact error with two terms:

* the outer part of the `N`-box removed when trimming to side-`D` blocks;
* the carry-transition set inside the trimmed box.

This file converts that exact expression into the standard power estimate.
Under `2 * D ≤ N`, the trimmed side is at least `N / 2`; hence its
`t`-dimensional volume loses at most a factor `2^t`.  Combining this with
the existing codimension-one carry-transition count gives an explicit
`O_{k,|κ|}(D/N)` bound.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Dividing by the trimmed volume costs at most `2^t` relative to dividing
by the full volume. -/
theorem solution
    {D N t : ℕ} (hD : 0 < D) (hfit : 2 * D ≤ N)
    {a A : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) :
    a / (trimToMultiple D N : ℝ) ^ t ≤
      A * (2 : ℝ) ^ t / (N : ℝ) ^ t := by
  have hN : 0 < N := by omega
  have htrim : 0 < trimToMultiple D N := by
    have hhalf := le_two_mul_trimToMultiple hD hfit
    omega
  have hNpow : 0 < (N : ℝ) ^ t := by positivity
  have htrimpow :
      0 < (trimToMultiple D N : ℝ) ^ t := by
    positivity
  have hpow :=
    pow_le_two_pow_mul_trimToMultiple_pow
      (t := t) hD hfit
  have hinv :
      (1 : ℝ) / (trimToMultiple D N : ℝ) ^ t ≤
        (2 : ℝ) ^ t / (N : ℝ) ^ t := by
    rw [div_le_div_iff₀ htrimpow hNpow]
    simpa only [one_mul] using hpow
  have hA : 0 ≤ A := ha.trans haA
  calc
    a / (trimToMultiple D N : ℝ) ^ t =
        a * ((1 : ℝ) /
          (trimToMultiple D N : ℝ) ^ t) := by ring
    _ ≤ A * ((1 : ℝ) /
          (trimToMultiple D N : ℝ) ^ t) := by
      gcongr
    _ ≤ A * ((2 : ℝ) ^ t /
          (N : ℝ) ^ t) := by
      gcongr
    _ = A * (2 : ℝ) ^ t / (N : ℝ) ^ t := by
      ring
