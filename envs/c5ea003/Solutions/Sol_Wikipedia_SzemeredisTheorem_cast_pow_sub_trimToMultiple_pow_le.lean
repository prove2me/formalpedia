-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cast_pow_sub_trimToMultiple_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:33.672181+00:00
-- url     : https://prove2.me/submissions/bbf28411-7685-4a44-b755-65e952bd6829

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
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
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
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
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
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
/-!
# Finite-box congruence boundaries for the CFZ divisor expansion

This file isolates the exact finite-box step between the divisor expansion
and the prime-local arithmetic.  It has three layers.

* A normalized boundary estimate compares a bounded periodic function on a
  natural box with its exact residue-class mean.
* Coordinatewise `Fin`/`ZMod` equivalences identify the mean on a
  `CubePoint k N` with the corresponding natural box mean.
* For the cyclic representative used by `cfzWTrickedLinearValue`, periodicity
  modulo a divisor modulus `D` is proved under the precise compatibility
  hypothesis `D ∣ W * N`.

The compatibility hypothesis in the last item is mathematically necessary
for this direct rectangular trimming argument: reducing a form modulo `N`
can change an integer lift by a multiple of `N`, and the subsequent
`W`-trick changes its value by a multiple of `W * N`.  Without divisibility
by `D`, an unconditional treatment must subdivide the box into carry cells
on which every modular reduction has a fixed integer lift.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Why cyclic representatives need a compatibility or carry argument -/
/-! ## Weighted lifts through two moduli -/
/-! ## Natural representatives of CFZ cube points -/
/-! ## Canonical carry cells -/
/-! ## Divisibility indicators modulo a common multiple -/
/-! ## Exact finite-box and residue-vector reindexing -/
/-! ## Reindexing the cyclic CFZ cube -/
/-! ## CFZ periodicity under lift compatibility -/
/-! ## The exact affine residue model -/
/-! ## Normalized trimming loss -/
/-! ## Paired divisibility specialization -/

open Wikipedia.SzemeredisTheorem in
/-- The exact boundary cardinality of a constant-side box is at most
`D * t * N^(t-1)`. -/
theorem solution
    {D N t : ℕ} (hD : 0 < D) :
    (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
      (D : ℝ) * (t : ℝ) * (N : ℝ) ^ (t - 1) := by
  have htrimle : trimToMultiple D N ≤ N :=
    trimToMultiple_le D N
  have hpowle :
      (trimToMultiple D N) ^ t ≤ N ^ t :=
    Nat.pow_le_pow_left htrimle t
  have hdiff :
      N - trimToMultiple D N ≤ D :=
    (trimToMultiple_boundary_lt (L := N) hD).le
  have hcastdiff :
      (N : ℝ) - (trimToMultiple D N : ℝ) =
        ((N - trimToMultiple D N : ℕ) : ℝ) := by
    rw [Nat.cast_sub htrimle]
  have hnonneg :
      0 ≤ (N : ℝ) ^ t -
        (trimToMultiple D N : ℝ) ^ t := by
    exact sub_nonneg.mpr (pow_le_pow_left₀
      (by positivity) (by exact_mod_cast htrimle) t)
  calc
    (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) =
        (N : ℝ) ^ t -
          (trimToMultiple D N : ℝ) ^ t := by
      rw [Nat.cast_sub hpowle]
      norm_num only [Nat.cast_pow]
    _ = |(N : ℝ) ^ t -
          (trimToMultiple D N : ℝ) ^ t| :=
      (abs_of_nonneg hnonneg).symm
    _ ≤ |(N : ℝ) - (trimToMultiple D N : ℝ)| *
          (t : ℝ) *
          max |(N : ℝ)| |(trimToMultiple D N : ℝ)| ^ (t - 1) :=
      abs_pow_sub_pow_le (N : ℝ) (trimToMultiple D N : ℝ) t
    _ = ((N - trimToMultiple D N : ℕ) : ℝ) *
          (t : ℝ) * (N : ℝ) ^ (t - 1) := by
      rw [hcastdiff, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg _),
        max_eq_left (by exact_mod_cast htrimle)]
    _ ≤ (D : ℝ) * (t : ℝ) * (N : ℝ) ^ (t - 1) := by
      gcongr
