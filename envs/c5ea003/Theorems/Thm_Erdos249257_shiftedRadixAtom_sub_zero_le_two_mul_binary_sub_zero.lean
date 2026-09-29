-- Prove2me | Theorems.Thm_Erdos249257_shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero
-- name    : Erdos249257.shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T21:08:19.412061+00:00
-- url     : https://prove2.me/theorems/775b2d78-cec6-491e-9d71-7872dbcf2650
-- title:
--   Radix atom displacement is bounded by binary displacement
-- statement:
--   For every integer base b≥2 and indices N,d, the change in the shifted radix atom from shift 0 to N is at most twice the corresponding change for the binary Mersenne atom.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L268-L347
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
import Definitions.Def_Erdos249257_ReciprocalSupportIrrationality
import Definitions.Def_Erdos249257_AllBaseReciprocalSupportIrrationality
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
# Reciprocal-summable support irrationality at every integer base

The binary close-return theorem is stronger than its original statement
suggests. For every radix b ≥ 2, the displacement of a periodic tail atom
from its zero-shift value is at most twice the corresponding binary
displacement. Hence the binary LCM/Cesàro close returns are simultaneous
close returns at every integer base. An exact integer-orbit argument then
rules out rationality.

This yields the unconditional theorem

  A.Infinite → Summable (reciprocalSupportTerm A) →
    Irrational (erdosSupportSeries b A)

for every integer b ≥ 2, without pairwise coprimality, periodicity, density,
or a powerful-support hypothesis.
-/


open Filter Set

noncomputable section



























/-! ## Binary-to-radix displacement transfer -/

open Erdos249257

theorem Erdos249257.shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero
    (b N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixAtom b N d - shiftedRadixAtom b 0 d ≤
      2 * (shiftedMersenneAtom N d - shiftedMersenneAtom 0 d) := by sorry
