-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.sum_kernelWeight_gcdOrbit_block
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:07:35.705116+00:00
-- url     : https://prove2.me/submissions/6a77df30-7dd5-4df9-be6b-921a9a8d4d92

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_sum_kernelWeight_gcdOrbit
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Tactic
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

namespace Erdos257PeriodNoncollapse.TotientTailPeriodKiller
end Erdos257PeriodNoncollapse.TotientTailPeriodKiller

/-!
# Real-base complete-orbit bookkeeping

Generalises the *repaired existing* binary proof in
Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean, lines 153--280,
without changing its finite permutation argument. Unlike the binary result,
this applies at B=2^α for α arbitrarily close to zero.
NOT COMPILED in this return. No premise is an irrationality conclusion.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB : 1 < B)
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (b : ℕ) :
    (∑ j ∈ Finset.range (d / Nat.gcd L d),
      kernelWeight B d ((b * (d / Nat.gcd L d) + j + 1) * L)) =
      1 / (B ^ Nat.gcd L d - 1) := by
  let g := Nat.gcd L d
  let q := L / g
  let h := d / g
  have hLfac : g * q = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L d)
  have hdfac : g * h = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right L d)
  have hperiod : d ∣ h * L := by
    refine ⟨q, ?_⟩
    rw [← hdfac, ← hLfac]
    ring
  have heq :
      (∑ j ∈ Finset.range (d / Nat.gcd L d),
        kernelWeight B d ((b * (d / Nat.gcd L d) + j + 1) * L)) =
      ∑ j ∈ Finset.range (d / Nat.gcd L d), kernelWeight B d ((j + 1) * L) := by
    apply Finset.sum_congr rfl
    intro j _hj
    unfold kernelWeight
    apply congrArg (fun z : ℕ => B ^ z / (B ^ d - 1))
    change ((b * h + j + 1) * L) % d = ((j + 1) * L) % d
    have hdecomp : (b * h + j + 1) * L = b * (h * L) + (j + 1) * L := by ring
    have hbperiod : d ∣ b * (h * L) := dvd_mul_of_dvd_right hperiod b
    rw [hdecomp, Nat.add_mod, Nat.mod_eq_zero_of_dvd hbperiod, zero_add]
    exact Nat.mod_mod _ _
  rw [heq]
  exact sum_kernelWeight_gcdOrbit B hB L d hL hd
end
