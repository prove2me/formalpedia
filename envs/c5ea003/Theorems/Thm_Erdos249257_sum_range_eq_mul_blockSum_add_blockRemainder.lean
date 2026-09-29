-- Prove2me | Theorems.Thm_Erdos249257_sum_range_eq_mul_blockSum_add_blockRemainder
-- name    : Erdos249257.sum_range_eq_mul_blockSum_add_blockRemainder
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T21:56:13.508691+00:00
-- url     : https://prove2.me/theorems/f04e91ea-3b5d-4d5f-979e-43c38f428452
-- title:
--   Finite sum splits into complete blocks and a remainder
-- statement:
--   When every block of length h in a real sequence has sum S, the sum of the first N entries equals the number N/h of complete blocks, rounded down, times S plus the remainder from the unfinished block.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/RationalSupportCarrySkeleton.lean#L1139-L1161
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

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


open ArithmeticFunction Filter Set

/-! ## Doubling residues and wrap digits -/

























/-! ## Generic finite-cycle identities -/













/-! ## One-wrap classification -/

















/-! ## The actual multiplicative order of two -/













/-! ## Odd-denominator tail states -/











/-! ## Rational fractions construct the odd tail state -/











/-! ## Reciprocal mass and Cesàro order bounds -/

open Erdos249257

theorem Erdos249257.sum_range_eq_mul_blockSum_add_blockRemainder
    (x : ℕ → ℝ) (h : ℕ) (blockSum : ℝ)
    (hblock : ∀ q : ℕ,
      ∑ j ∈ Finset.range h, x (q * h + j) = blockSum)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, x n =
      ((N / h : ℕ) : ℝ) * blockSum + blockRemainder x h N := by sorry
