-- Prove2me | solution 1 for ErdosProblems.Erdos257.irrational_erdosSupportSeries_of_radix_closeReturn
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:28:01.674921+00:00
-- url     : https://prove2.me/submissions/913a5664-1ae8-4bcf-b6fc-7f7a4c574a46

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
import Theorems.Thm_Erdos249257_hasRationalValue_iff_not_irrational
import Theorems.Thm_Erdos249257_shiftedRadixSupportAtom_zero_strictMinimum
import Theorems.Thm_Erdos249257_tsum_shiftedRadixSupportAtom_step
import Theorems.Thm_Erdos249257_tsum_shiftedRadixSupportAtom_zero
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

namespace Erdos257PeriodNoncollapse
end Erdos257PeriodNoncollapse

namespace ErdosProblems.Erdos257
end ErdosProblems.Erdos257

/-! # Irrationality from arbitrarily close radix returns -/

namespace ErdosProblems.Erdos257
open Erdos257PeriodNoncollapse Filter
noncomputable section
end
end ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse Filter
open ErdosProblems in
open ErdosProblems.Erdos257 in
theorem solution
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      (∑' d : ℕ, Erdos249257.shiftedRadixSupportAtom b A N d) <
        (∑' d : ℕ, Erdos249257.shiftedRadixSupportAtom b A 0 d) + ε) :
    Irrational (Erdos249257.erdosSupportSeries b A) := by
  by_contra hrat
  have hvalue : Erdos249257.HasRationalValue (Erdos249257.erdosSupportSeries b A) :=
    (Erdos249257.hasRationalValue_iff_not_irrational _).2 hrat
  obtain ⟨p, v, hv, hratValue⟩ := hvalue
  let T : ℕ → ℝ := fun N =>
    ∑' d : ℕ, Erdos249257.shiftedRadixSupportAtom b A N d
  let u : ℕ → ℤ := Nat.rec p
    (fun N z => (b : ℤ) * z - ((v * Erdos249257.supportCoeff A (N + 1) : ℕ) : ℤ))
  have hu0 : u 0 = p := rfl
  have huSucc : ∀ N : ℕ,
      u (N + 1) =
        (b : ℤ) * u N - ((v * Erdos249257.supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    rfl
  have hT0 : T 0 = Erdos249257.erdosSupportSeries b A := by
    exact Erdos249257.tsum_shiftedRadixSupportAtom_zero b A
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have huCast : ∀ N : ℕ, ((u N).cast : ℝ) = (v : ℝ) * T N := by
    intro N
    induction N with
    | zero =>
        rw [hu0, hT0, hratValue]
        field_simp
    | succ N ih =>
        rw [huSucc]
        push_cast
        rw [ih]
        have hstep := Erdos249257.tsum_shiftedRadixSupportAtom_step b A N hb
        change (b : ℝ) * ((v : ℝ) * T N) -
            (v : ℝ) * Erdos249257.supportCoeff A (N + 1) = (v : ℝ) * T (N + 1)
        change (b : ℝ) * T N - T (N + 1) =
            Erdos249257.supportCoeff A (N + 1) at hstep
        nlinarith
  obtain ⟨N, hN, hnear⟩ :=
    hclose (1 / (v : ℝ)) (by positivity)
  have hstrict :=
    Erdos249257.shiftedRadixSupportAtom_zero_strictMinimum b A hb hA N hN
  have hstrictT : T 0 < T N := by
    simpa [T] using hstrict
  have hnearT : T N < T 0 + 1 / (v : ℝ) := by
    simpa [T] using hnear
  have hgapPos : (0 : ℝ) < ((u N - u 0 : ℤ) : ℝ) := by
    push_cast
    rw [huCast N, huCast 0]
    nlinarith [mul_pos hvR (sub_pos.mpr hstrictT)]
  have hgapLt : ((u N - u 0 : ℤ) : ℝ) < 1 := by
    push_cast
    rw [huCast N, huCast 0]
    have htailGap : T N - T 0 < 1 / (v : ℝ) := by
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hnearT)
    have hmul := mul_lt_mul_of_pos_left htailGap hvR
    have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
    rw [show (v : ℝ) * (1 / (v : ℝ)) = 1 by field_simp] at hmul
    nlinarith
  have hgapPosInt : 0 < u N - u 0 := by exact_mod_cast hgapPos
  have hgapLtInt : u N - u 0 < 1 := by exact_mod_cast hgapLt
  omega
