-- Prove2me | solution 1 for Erdos249257.shiftedRadixAtom_step
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:17:16.385817+00:00
-- url     : https://prove2.me/submissions/4d371827-32bf-4cd1-8f2c-06231ff51fc8

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

namespace Erdos249257
open Filter Set

noncomputable section
end
end Erdos249257

open Filter Set
open Erdos249257 in
theorem solution
    (b N d : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * shiftedRadixAtom b N d -
        shiftedRadixAtom b (N + 1) d =
      if 0 < d ∧ d ∣ N + 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [shiftedRadixAtom]
  · have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hb)
    by_cases hd1 : d = 1
    · subst d
      have hden1 : (b : ℝ) - 1 ≠ 0 := by linarith
      simp only [shiftedRadixAtom, one_ne_zero, if_false, Nat.mod_one,
        pow_zero, Nat.zero_lt_one, Nat.one_dvd, and_self, if_true, pow_one]
      field_simp [hden1]
    have hone : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
    have hsuccmod : (N + 1) % d = (N % d + 1) % d := by
      rw [Nat.add_mod, hone]
    have hden : (b : ℝ) ^ d - 1 ≠ 0 := by
      have : (1 : ℝ) < (b : ℝ) ^ d := one_lt_pow₀ hb1 hd.ne'
      linarith
    by_cases hwrap : d ∣ N + 1
    · have hsucc : (N + 1) % d = 0 := Nat.mod_eq_zero_of_dvd hwrap
      have hmodlt : N % d < d := Nat.mod_lt _ hd
      have hmod : N % d + 1 = d := by
        have hdvd : d ∣ N % d + 1 := by
          apply Nat.dvd_of_mod_eq_zero
          rw [← hsuccmod]
          exact hsucc
        have hle : d ≤ N % d + 1 := Nat.le_of_dvd (by omega) hdvd
        omega
      rw [if_pos ⟨hd, hwrap⟩]
      simp only [shiftedRadixAtom, if_neg hd.ne', hsucc, pow_zero]
      rw [show N % d = d - 1 by omega]
      have hpow :
          (b : ℝ) * (b : ℝ) ^ (d - 1) = (b : ℝ) ^ d := by
        calc
          (b : ℝ) * (b : ℝ) ^ (d - 1) =
              (b : ℝ) ^ (d - 1) * b := by ring
          _ = (b : ℝ) ^ ((d - 1) + 1) := (pow_succ _ _).symm
          _ = (b : ℝ) ^ d := by congr 1; omega
      field_simp [hden]
      rw [hpow]
    · have hsucc0 : (N + 1) % d ≠ 0 := by
        intro hzero
        exact hwrap (Nat.dvd_of_mod_eq_zero hzero)
      have hmodlt : N % d < d := Nat.mod_lt _ hd
      have hnextlt : N % d + 1 < d := by
        have hle : N % d + 1 ≤ d := by omega
        apply lt_of_le_of_ne hle
        intro heq
        apply hsucc0
        rw [hsuccmod, heq, Nat.mod_self]
      have hsucc : (N + 1) % d = N % d + 1 := by
        rw [hsuccmod, Nat.mod_eq_of_lt hnextlt]
      rw [if_neg (fun h => hwrap h.2)]
      simp only [shiftedRadixAtom, if_neg hd.ne', hsucc]
      rw [pow_succ]
      ring
