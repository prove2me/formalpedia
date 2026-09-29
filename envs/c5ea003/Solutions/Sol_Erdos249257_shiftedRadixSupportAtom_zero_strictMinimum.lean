-- Prove2me | solution 1 for Erdos249257.shiftedRadixSupportAtom_zero_strictMinimum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:23:28.301712+00:00
-- url     : https://prove2.me/submissions/0c82eec0-1e89-4572-afef-a755e2b29d20

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
import Theorems.Thm_Erdos249257_shiftedRadixAtom_zero_le
import Theorems.Thm_Erdos249257_summable_shiftedRadixSupportAtom
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

theorem shiftedRadixAtom_zero
    (b d : ℕ) :
    shiftedRadixAtom b 0 d = (1 : ℝ) / ((b : ℝ) ^ d - 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · simp [shiftedRadixAtom, hd.ne']



theorem shiftedRadixAtom_zero_lt_of_lt
    (b N d : ℕ) (hb : 2 ≤ b) (hN : 0 < N) (hNd : N < d) :
    shiftedRadixAtom b 0 d < shiftedRadixAtom b N d := by
  have hd : 0 < d := hN.trans hNd
  rw [shiftedRadixAtom_zero, shiftedRadixAtom, if_neg hd.ne',
    Nat.mod_eq_of_lt hNd]
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
  have hden : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
    linarith
  exact div_lt_div_of_pos_right (one_lt_pow₀ hb1 hN.ne') hden
end
end Erdos249257

open Filter Set
open Erdos249257 in
theorem solution
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (N : ℕ) (hN : 0 < N) :
    (∑' d : ℕ, shiftedRadixSupportAtom b A 0 d) <
      ∑' d : ℕ, shiftedRadixSupportAtom b A N d := by
  obtain ⟨d, hdA, hNd⟩ := hA.exists_gt N
  exact Summable.tsum_lt_tsum_of_nonneg (i := d)
    (fun e => Set.indicator_nonneg
      (fun k _ => shiftedRadixAtom_nonneg b 0 k hb) e)
    (fun e => by
      classical
      by_cases heA : e ∈ A
      · simpa [shiftedRadixSupportAtom, heA] using
          shiftedRadixAtom_zero_le b N e hb
      · simp [shiftedRadixSupportAtom, heA])
    (by
      simpa [shiftedRadixSupportAtom, hdA] using
        shiftedRadixAtom_zero_lt_of_lt b N d hb hN hNd)
    (summable_shiftedRadixSupportAtom b A N hb)
