-- Prove2me | solution 1 for ErdosProblems.Erdos257.sum_half_pow_le_twice_min
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:33:41.083975+00:00
-- url     : https://prove2.me/submissions/c9ed87f9-9496-4a2f-a4f5-663da0e0e792

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

namespace TotientTailPeriodKiller
end TotientTailPeriodKiller

/-!
# Finite averaging for divisibility-weighted supports

The weighted support proof needs two finite estimates before taking any
limit. The orbit estimate retains the geometric GCD factor discarded by the
reciprocal-mass bound. The observation-length estimate sums incomplete-period
errors across dyadic scales, charging each conductor only once.

These are the actual finite estimates used in the analytic proof. The
prime-part decomposition and the final choice of scales are separate steps.
-/

namespace ErdosProblems.Erdos257
open Erdos257PeriodNoncollapse TotientTailPeriodKiller

noncomputable section
end
end ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse TotientTailPeriodKiller
open ErdosProblems in
open ErdosProblems.Erdos257 in
theorem solution (s : Finset ℕ) (m : ℕ)
    (hm : ∀ j ∈ s, m ≤ j) :
    ∑ j ∈ s, (1 / 2 : ℝ) ^ j ≤ 2 * (1 / 2 : ℝ) ^ m := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => j - m) s := by
    intro i hi j hj hij
    have := hm i hi
    have := hm j hj
    dsimp at hij
    omega
  have hgeom := summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have htail : ∑ j ∈ s, (1 / 2 : ℝ) ^ (j - m) ≤ 2 := by
    rw [← Finset.sum_image hinj]
    calc
      _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
        hgeom.sum_le_tsum _ (fun _ _ => by positivity)
      _ = 2 := by rw [tsum_geometric_of_abs_lt_one (by norm_num)]; norm_num
  calc
    ∑ j ∈ s, (1 / 2 : ℝ) ^ j =
        (1 / 2 : ℝ) ^ m * ∑ j ∈ s, (1 / 2 : ℝ) ^ (j - m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← pow_add, Nat.add_sub_of_le (hm j hj)]
    _ ≤ (1 / 2 : ℝ) ^ m * 2 := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring
