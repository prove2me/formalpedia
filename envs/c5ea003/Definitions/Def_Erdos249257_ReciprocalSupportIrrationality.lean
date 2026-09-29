-- Prove2me | Definitions.Def_Erdos249257_ReciprocalSupportIrrationality
-- name    : Erdos249257_ReciprocalSupportIrrationality
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:27:29.316528+00:00
-- url     : https://prove2.me/theorems/0234cd71-854f-42b5-90fd-fb4fbe35e641
-- title:
--   Shifted binary Mersenne atoms on a support
-- statement:
--   This bundle defines the base-two shifted Mersenne atom 2^(N mod d)/(2^d−1) for nonzero d, zero at d=0, and its restriction to a support set A.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/ReciprocalSupportIrrationality.lean#L1-L1585
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
# Reciprocal-summable support irrationality

This module develops the shifted-atom description of binary support tails.
-/

namespace Erdos249257

open Filter Set
open TotientTailPeriodKiller

noncomputable section

/-- The contribution of support rank `d` to the binary coefficient tail at
shift `N`.  Rank zero is normalized to zero, consistently with
`erdosSupportSeries`. -/
noncomputable def shiftedMersenneAtom (N d : ℕ) : ℝ :=
  if d = 0 then 0
  else (2 : ℝ) ^ (N % d) / ((2 : ℝ) ^ d - 1)

/-- The shifted atom restricted to a support set. -/
noncomputable def shiftedSupportAtom (A : Set ℕ) (N d : ℕ) : ℝ :=
  Set.indicator A (shiftedMersenneAtom N) d





/-! ## GCD orbit means -/













































































/-! ## The integer-gap endgame -/









/-! ## Generalised integer-gap endgame -/





/-! ## Pratt's shift identity -- the arithmetic core

Pratt (arXiv:2409.15185, Proposition 2.1) forces `omega` to reproduce its own head,
shifted by one, across a block of consecutive integers.  The load-bearing step is
purely arithmetic and is isolated here; the prime `k`-tuples input enters only as the
primality hypothesis `hp`. -/












/-! ## Finite tail splitting, and the shifted-block identity -/


























/-! ## What the witness hypothesis costs: the block length must diverge -/






/-! ## The parity obstruction to the Erdos 1948 zero-run mechanism -/











/-! ## The two-powers-apart obstruction behind the `A*` block cap -/




/-! ## Erdos problem 69 at the witness boundary -/










end
end Erdos249257


