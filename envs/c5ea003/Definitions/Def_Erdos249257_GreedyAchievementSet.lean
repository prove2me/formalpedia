-- Prove2me | Definitions.Def_Erdos249257_GreedyAchievementSet
-- name    : Erdos249257_GreedyAchievementSet
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:23:11.818746+00:00
-- url     : https://prove2.me/theorems/725d9584-b411-470b-9170-85d91a2e10e9
-- title:
--   Greedy Mersenne weights, remainders, and phase separation
-- statement:
--   This bundle defines rational Mersenne weights, a greedy remainder recurrence, a scaled second-channel phase for the target 1/2, and a decidable separation predicate comparing that phase with 1/3.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/GreedyAchievementSet.lean#L1-L3361
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
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
# Greedy geometry for the Mersenne achievement set

For positive exponents put `w(n) = 1 / (2^n - 1)` and let `T(n)` be the
mass strictly after exponent `n`.  This file formalizes the dependency-critical
part of the greedy-achievement route for Erdős problem #257:

* summability, tail recurrence, and the strict superincreasing inequality;
* the quantitative gap asymptotic `(2/3)·4⁻ⁿ + O(8⁻ⁿ)` with an explicit
  higher-channel remainder bound;
* normalized support coding through the existing `erdosSupportSeries`;
* compactness and perfection from a continuous injective binary coding;
* nested finite-cylinder stages, their exact Lebesgue measures, and continuity
  from above;
* the measure-one and nowhere-dense conclusions, hence the precise fat-Cantor
  status of the achievement set;
* exact real and rational greedy recurrences;
* the all-level survival characterization, with the necessary nonnegativity
  guard made explicit;
* finite rational upper enclosures for tails and sound death certificates;
* the exact level-one death certificate for `3/4`;
* uniqueness of normalized support coding and computability of the digits of
  a rational value already known to belong to the achievement set.

`CertifiedGreedyMersenneDeath` is one-sided: a certificate proves
nonmembership, while
failure to find a certificate or survival through any finite depth proves
nothing about membership.  The index-zero support bit is normalized away
because its analytic weight is zero.  Nothing here settles the universal
problem, and no finite computation is promoted to an infinite-support claim.

No novelty or priority claim is made for the theorems in this file.
-/

namespace Erdos249257

open scoped ENNReal

open Filter Set MeasureTheory Topology

/-! ## Weights and tails -/

/-- The exact rational Mersenne weight `1 / (2^n - 1)`.  Its meaningful
support indices are positive; at index zero Lean's division convention gives
zero. -/
def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)





































/-! ## Quantitative gap asymptotic -/







































/-! ## Normalized support coding -/





















/-! ## Binary coding, compactness, and perfection -/

























/-! ## Nested cylinder stages -/



































/-! ## Exact cylinder measures and the measure-one limit -/















/-! ## Exact greedy recurrences -/



/-- Exact rational version of the greedy residual. -/
def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n









/-! ## Exact rational sliver coordinates

The sharp skip-branch analysis is most naturally expressed after doubling
the usual dyadic excess coordinate.  This normalization is deliberate: it
makes the constant term in a selected-step update exactly `-2`, so the
limiting affine map is `ρ ↦ 4 * ρ - 2` and its fixed point is `2 / 3`.
The undoubled coordinate has constant term `-1` and fixed point `1 / 3`.
-/















/-! ## Skipped-branch cap transport -/



































/-! ## Recovery, survival, and uniqueness -/





















/-! ## Fatal-state dichotomy -/





















/-! ## No isolated points -/













/-! ## Total disconnectedness and nowhere density -/







/-! ## Finite exact-rational death certificates -/



















/-! ## Rational greedy prefixes and computable digits -/















/-! ## Exact regression fixtures -/



/-! ## Half-prefix forcing and the dyadic boundary obstruction

The finite greedy computation for the target `1/2` admits a sharper
interpretation than level-by-level survival.  Splitting each Mersenne weight
into its binary skeleton and a positive correction turns a sufficiently long
support prefix into a narrow interval for the correction value.  If those
intervals are trapped in compatible dyadic cylinders of unbounded depth, the
correction and complementary-binary values coincide, giving an exact support
identity.  This section formalizes that coinductive limit interface and the
elementary arithmetic at a crossed dyadic boundary.  It does *not* prove that
the generated forcing chain is unbounded.
-/

















/-! ## Exact finite-block sliver return geometry -/































/-! ## Exact sliver-normalization regression fixtures -/



































/-! ## Greedy shadows and the second-channel separation interface -/









































/-- Rational form of the second-channel phase.  Its branch arithmetic can be
proved over `ℚ` and then transferred to the real coordinate below. -/
def greedyMersenneSecondChannelPhaseRat (n : ℕ) : ℚ :=
  (4 : ℚ) ^ n *
    (2 * greedyMersenneRemainderRat (1 / 2 : ℚ) n
      - ((1 : ℚ) / 2) ^ n)











/-- Decidable rational form of the shrinking-hole avoidance condition. -/
def HalfSecondChannelSeparatedRat (n : ℕ) : Prop :=
  (1 / 6 : ℚ) + (37 / 56 : ℚ) * ((1 : ℚ) / 2) ^ n
    ≤ |greedyMersenneSecondChannelPhaseRat n - 1 / 3|



/-!
The recurrence and predecessor windows above identify an exact arithmetic
frontier, but they do not rule out visits to `(0, 1)`.  Consequently they do
not prove that one half is absent from the Mersenne achievement set and do not
settle Erdős #257.
-/

instance (n : ℕ) : Decidable (HalfSecondChannelSeparatedRat n) :=
  by
    unfold HalfSecondChannelSeparatedRat
    infer_instance










































end Erdos249257


