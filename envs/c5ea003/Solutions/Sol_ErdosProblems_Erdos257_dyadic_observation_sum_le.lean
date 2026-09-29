-- Prove2me | solution 1 for ErdosProblems.Erdos257.dyadic_observation_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:07:37.083911+00:00
-- url     : https://prove2.me/submissions/75a69929-46b8-46db-90d0-1772d3d7bf4f

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
import Theorems.Thm_ErdosProblems_Erdos257_sum_dyadic_observation_weights_le
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
theorem solution (J F : Finset ℕ) (Q : ℕ) (α : ℕ → ℝ)
    (hF : ∀ a ∈ F, 0 < a) (hα : ∀ a ∈ F, 0 ≤ α a) :
    (∑ j ∈ J, (1 / 2 : ℝ) ^ j *
      ∑ a ∈ F.filter (fun a => a ≤ Q * 2 ^ j), α a) ≤
      2 * (Q : ℝ) * ∑ a ∈ F, α a / a := by
  classical
  calc
    _ = ∑ a ∈ F, α a *
        ∑ j ∈ J.filter (fun j => a ≤ Q * 2 ^ j), (1 / 2 : ℝ) ^ j := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ ≤ ∑ a ∈ F, α a * (2 * (Q : ℝ) / a) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (sum_dyadic_observation_weights_le J Q a (hF a ha)) (hα a ha)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring
