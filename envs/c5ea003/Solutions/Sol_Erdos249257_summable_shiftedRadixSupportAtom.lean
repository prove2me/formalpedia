-- Prove2me | solution 1 for Erdos249257.summable_shiftedRadixSupportAtom
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:13:40.739974+00:00
-- url     : https://prove2.me/submissions/5a45fd27-3d5b-4e62-8ee5-5521f065ead7

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
import Theorems.Thm_Erdos249257_summable_erdosSupport_indicator
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

namespace Erdos249257
open Filter Set

noncomputable section





theorem shiftedRadixAtom_nonneg
    (b N d : ℕ) (hb : 2 ≤ b) :
    0 ≤ shiftedRadixAtom b N d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · rw [shiftedRadixAtom, if_neg hd.ne']
    have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    have hden : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
      linarith
    positivity







theorem shiftedRadixAtom_le_pow_mul_zero
    (b N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixAtom b N d ≤
      (b : ℝ) ^ N * ((1 : ℝ) / ((b : ℝ) ^ d - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · rw [shiftedRadixAtom, if_neg hd.ne']
    have hb0 : (1 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (le_trans (by norm_num) hb)
    have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    have hden : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
      have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
      linarith
    have hmod : N % d ≤ N := Nat.mod_le _ _
    have hp : (b : ℝ) ^ (N % d) ≤ (b : ℝ) ^ N :=
      pow_le_pow_right₀ hb0 hmod
    calc
      (b : ℝ) ^ (N % d) / ((b : ℝ) ^ d - 1) =
          (b : ℝ) ^ (N % d) * (1 / ((b : ℝ) ^ d - 1)) := by ring
      _ ≤ (b : ℝ) ^ N * (1 / ((b : ℝ) ^ d - 1)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
end
end Erdos249257

open Filter Set
open Erdos249257 in
theorem solution
    (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    Summable (shiftedRadixSupportAtom b A N) := by
  have hbase := summable_erdosSupport_indicator b A hb
  have hscaled : Summable (fun d : ℕ =>
      (b : ℝ) ^ N *
        Set.indicator A (fun d => (1 : ℝ) / ((b : ℝ) ^ d - 1)) d) :=
    hbase.mul_left ((b : ℝ) ^ N)
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hscaled
  · exact Set.indicator_nonneg
      (fun d _ => shiftedRadixAtom_nonneg b N d hb) d
  · by_cases hdA : d ∈ A
    · simp only [shiftedRadixSupportAtom, Set.indicator_of_mem hdA]
      exact shiftedRadixAtom_le_pow_mul_zero b N d hb
    · simp [shiftedRadixSupportAtom, hdA]
