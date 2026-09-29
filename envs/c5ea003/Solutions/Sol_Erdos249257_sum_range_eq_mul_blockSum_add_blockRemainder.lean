-- Prove2me | solution 1 for Erdos249257.sum_range_eq_mul_blockSum_add_blockRemainder
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:02:19.754562+00:00
-- url     : https://prove2.me/submissions/91d2f298-0a51-402d-bcb3-89acec67158f

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Definitions.Def_Erdos249257_GenericTailOrbitRigidity
import Definitions.Def_Erdos249257_GreedyAchievementSet
import Definitions.Def_Erdos249257_RationalSupportCarrySkeleton
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Perfect

/-!
# Rational support, doubling residues, and reciprocal mass

Suppose the base-two support series has a rational value whose denominator is
written as `2^c * v`, with `v` odd.  Clearing that denominator produces a
positive integer tail state.  Modulo `v`, the state follows a doubling orbit,
and the wrap digits record exactly when doubling crosses the modulus.  The
finite arithmetic begins with the identity

`sum residues = odd modulus * number of wraps`.

When the reciprocal support terms are summable, the Cesàro mean of the support
tails is their sum `reciprocalMass A`.  Combining this mean identity with the
periodic residue arithmetic gives quantitative lower bounds from wrap
frequency and from Boolean collisions.  Common multiples also force every
positive tail state attached to an infinite support to be unbounded.

These are conditional obstructions, not a solution of Erdős #257.  They do
not exclude every rational denominator, and the nonsummable alternative below
is not stated as convergence of partial sums to `+∞`.  Exponent zero remains
excluded from the literal support semantics.  The finite computations at the
end only check examples; the general theorems are proved independently.
-/

namespace Erdos249257
open ArithmeticFunction Filter Set

/-! ## Doubling residues and wrap digits -/

























/-! ## Generic finite-cycle identities -/













/-! ## One-wrap classification -/

















/-! ## The actual multiplicative order of two -/













/-! ## Odd-denominator tail states -/











/-! ## Rational fractions construct the odd tail state -/











/-! ## Reciprocal mass and Cesàro order bounds -/



































/-- Exact partition of a prefix of length `M*h` into `M` consecutive
blocks of length `h`. -/
theorem sum_range_mul_eq_sum_blocks (x : ℕ → ℝ) (M h : ℕ) :
    ∑ n ∈ Finset.range (M * h), x n =
      ∑ q ∈ Finset.range M, ∑ j ∈ Finset.range h, x (q * h + j) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
end Erdos249257

open ArithmeticFunction Filter Set
open Erdos249257 in
theorem solution
    (x : ℕ → ℝ) (h : ℕ) (blockSum : ℝ)
    (hblock : ∀ q : ℕ,
      ∑ j ∈ Finset.range h, x (q * h + j) = blockSum)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, x n =
      ((N / h : ℕ) : ℝ) * blockSum + blockRemainder x h N := by
  have hlen : (N / h) * h + N % h = N := by
    simpa [mul_comm] using Nat.div_add_mod N h
  calc
    ∑ n ∈ Finset.range N, x n =
        ∑ n ∈ Finset.range ((N / h) * h + N % h), x n := by rw [hlen]
    _ = (∑ n ∈ Finset.range ((N / h) * h), x n) +
          blockRemainder x h N := by
      rw [Finset.sum_range_add]
      rfl
    _ = (∑ q ∈ Finset.range (N / h),
          ∑ j ∈ Finset.range h, x (q * h + j)) +
          blockRemainder x h N := by
      rw [sum_range_mul_eq_sum_blocks]
    _ = ((N / h : ℕ) : ℝ) * blockSum + blockRemainder x h N := by
      rw [Finset.sum_congr rfl fun q _ => hblock q]
      simp
