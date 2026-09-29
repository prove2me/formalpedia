-- Prove2me | solution 1 for Erdos249257.shiftedRadixAtom_sub_zero_le_two_mul_binary_sub_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:17:18.495981+00:00
-- url     : https://prove2.me/submissions/347932cc-10ae-4a32-a7ce-8fe2efbdcd6f

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
import Theorems.Thm_Erdos249257_shiftedMersenneAtom_zero
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







theorem shiftedRadixAtom_zero
    (b d : ℕ) :
    shiftedRadixAtom b 0 d = (1 : ℝ) / ((b : ℝ) ^ d - 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · simp [shiftedRadixAtom, hd.ne']



















/-! ## Binary-to-radix displacement transfer -/
end
end Erdos249257

open Filter Set
open Erdos249257 in
theorem solution
    (b N d : ℕ) (hb : 2 ≤ b) :
    shiftedRadixAtom b N d - shiftedRadixAtom b 0 d ≤
      2 * (shiftedMersenneAtom N d - shiftedMersenneAtom 0 d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom, shiftedMersenneAtom]
  let r := N % d
  have hrd : r < d := Nat.mod_lt _ hd
  by_cases hr0 : r = 0
  · simp [shiftedRadixAtom, shiftedMersenneAtom, hd.ne', r, hr0]
  have hr : 0 < r := Nat.pos_of_ne_zero hr0
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by linarith
  have hdenb : (0 : ℝ) < (b : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
    linarith
  have hden2 : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ d := one_lt_pow₀ (by norm_num) hd.ne'
    linarith
  have hk : 0 < d - r := Nat.sub_pos_of_lt hrd
  have hpowbk : (0 : ℝ) < (b : ℝ) ^ (d - r) := by positivity
  have hpow2k : (0 : ℝ) < (2 : ℝ) ^ (d - r) := by positivity
  have hpow2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hpowb_ge : (2 : ℝ) ^ (d - r) ≤ (b : ℝ) ^ (d - r) :=
    (pow_le_pow_left₀ (by norm_num) hbR) (d - r)
  have hupper :
      ((b : ℝ) ^ r - 1) / ((b : ℝ) ^ d - 1) ≤
        1 / (b : ℝ) ^ (d - r) := by
    rw [div_le_div_iff₀ hdenb hpowbk]
    have hpowadd : (b : ℝ) ^ r * (b : ℝ) ^ (d - r) = (b : ℝ) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have hone : (1 : ℝ) ≤ (b : ℝ) ^ (d - r) :=
      one_le_pow₀ (by linarith)
    calc
      ((b : ℝ) ^ r - 1) * (b : ℝ) ^ (d - r) =
          (b : ℝ) ^ r * (b : ℝ) ^ (d - r) -
            (b : ℝ) ^ (d - r) := by ring
      _ = (b : ℝ) ^ d - (b : ℝ) ^ (d - r) := by rw [hpowadd]
      _ ≤ (b : ℝ) ^ d - 1 := sub_le_sub_left hone _
      _ = 1 * ((b : ℝ) ^ d - 1) := by ring
  have hmiddle :
      1 / (b : ℝ) ^ (d - r) ≤ 1 / (2 : ℝ) ^ (d - r) := by
    exact one_div_le_one_div_of_le (by positivity) hpowb_ge
  have hlower :
      1 / (2 : ℝ) ^ (d - r) ≤
        2 * (((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ d - 1)) := by
    rw [div_le_iff₀ hpow2k]
    have hpowadd : (2 : ℝ) ^ r * (2 : ℝ) ^ (d - r) = (2 : ℝ) ^ d := by
      rw [← pow_add]
      congr 1
      omega
    have hhalf : (2 : ℝ) ^ r ≤ 2 * ((2 : ℝ) ^ r - 1) := by
      nlinarith
    have hdenne : (2 : ℝ) ^ d - 1 ≠ 0 := ne_of_gt hden2
    rw [div_eq_mul_inv]
    field_simp [hdenne]
    nlinarith
  rw [shiftedRadixAtom, if_neg hd.ne', shiftedRadixAtom_zero,
    shiftedMersenneAtom, if_neg hd.ne', shiftedMersenneAtom_zero]
  change ((b : ℝ) ^ r / ((b : ℝ) ^ d - 1) -
      1 / ((b : ℝ) ^ d - 1)) ≤
    2 * ((2 : ℝ) ^ r / ((2 : ℝ) ^ d - 1) -
      1 / ((2 : ℝ) ^ d - 1))
  have hleft :
      (b : ℝ) ^ r / ((b : ℝ) ^ d - 1) -
          1 / ((b : ℝ) ^ d - 1) =
        ((b : ℝ) ^ r - 1) / ((b : ℝ) ^ d - 1) := by ring
  have hright :
      (2 : ℝ) ^ r / ((2 : ℝ) ^ d - 1) -
          1 / ((2 : ℝ) ^ d - 1) =
        ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ d - 1) := by ring
  rw [hleft, hright]
  exact hupper.trans (hmiddle.trans hlower)
