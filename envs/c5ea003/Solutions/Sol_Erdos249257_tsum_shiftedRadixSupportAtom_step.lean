-- Prove2me | solution 1 for Erdos249257.tsum_shiftedRadixSupportAtom_step
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:23:32.170534+00:00
-- url     : https://prove2.me/submissions/22db4ed8-5833-498a-8cfb-b7f493e0c030

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
import Theorems.Thm_Erdos249257_shiftedRadixAtom_step
import Theorems.Thm_Erdos249257_summable_shiftedRadixSupportAtom
import Theorems.Thm_Erdos249257_supportCoeff_cast_eq_sum_indicator
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



















theorem shiftedRadixSupportAtom_step
    (b : ℕ) (A : Set ℕ) [DecidablePred (· ∈ A)]
    (N d : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * shiftedRadixSupportAtom b A N d -
        shiftedRadixSupportAtom b A (N + 1) d =
      if d ∈ A ∧ 0 < d ∧ d ∣ N + 1 then 1 else 0 := by
  classical
  by_cases hdA : d ∈ A
  · simp only [shiftedRadixSupportAtom, Set.indicator_of_mem hdA, hdA,
      true_and]
    exact shiftedRadixAtom_step b N d hb
  · simp [shiftedRadixSupportAtom, hdA]
end
end Erdos249257

open Filter Set
open Erdos249257 in
theorem solution
    (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * (∑' d : ℕ, shiftedRadixSupportAtom b A N d) -
        (∑' d : ℕ, shiftedRadixSupportAtom b A (N + 1) d) =
      (supportCoeff A (N + 1) : ℝ) := by
  classical
  have hsN := summable_shiftedRadixSupportAtom b A N hb
  have hsS := summable_shiftedRadixSupportAtom b A (N + 1) hb
  calc
    (b : ℝ) * (∑' d, shiftedRadixSupportAtom b A N d) -
          ∑' d, shiftedRadixSupportAtom b A (N + 1) d =
        (∑' d, (b : ℝ) * shiftedRadixSupportAtom b A N d) -
          ∑' d, shiftedRadixSupportAtom b A (N + 1) d := by
            rw [tsum_mul_left]
    _ = ∑' d, ((b : ℝ) * shiftedRadixSupportAtom b A N d -
          shiftedRadixSupportAtom b A (N + 1) d) :=
      ((hsN.mul_left (b : ℝ)).tsum_sub hsS).symm
    _ = ∑' d, (if d ∈ A ∧ 0 < d ∧ d ∣ N + 1 then 1 else 0) :=
      tsum_congr (shiftedRadixSupportAtom_step b A N · hb)
    _ = (supportCoeff A (N + 1) : ℝ) := by
      rw [tsum_eq_sum (s := (N + 1).divisors)]
      · rw [supportCoeff_cast_eq_sum_indicator]
        apply Finset.sum_congr rfl
        intro d hddiv
        have hdiv : d ∣ N + 1 := (Nat.mem_divisors.mp hddiv).1
        have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (by omega)
        by_cases hdA : d ∈ A
        · simp [hdA, hpos, hdiv]
        · simp [hdA]
      · intro d hdnot
        have hndvd : ¬ d ∣ N + 1 := by
          intro hdiv
          exact hdnot (Nat.mem_divisors.mpr ⟨hdiv, by omega⟩)
        simp [hndvd]
