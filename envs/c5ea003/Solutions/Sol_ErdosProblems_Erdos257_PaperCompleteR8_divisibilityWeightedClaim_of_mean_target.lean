-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim_of_mean_target
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:35:15.063776+00:00
-- url     : https://prove2.me/submissions/4c756457-6114-411f-914a-962edeecccfb

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_CoverPotentialBounds
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_MixedGaugeConsumer
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR7_all_base_hereditary_of_binary_returns
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_sample_lt_of_dyadicMean_lt
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_weighted_irrational_of_mean_target
import Mathlib
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

/-!
# Weighted mean + nonlinear cover test on ONE finite sampling scheme

The previous return's JointDyadicMeanSupply is a sufficient
condition, but is not the exact interface of the ordinary mixed proof: a small
fractional cover test need not give a small FIRST MOMENT of the displacement.
This module uses the correct nonlinear test. PositiveCoverData contributes no
remaining target. The concrete weighted finite-mean producer is isolated
here and proved, without additional premises, in WeightedReturn.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution
    (htarget : WeightedDyadicMeanTarget) : DivisibilityWeightedClaim := by
  constructor
  · intro b E hb hE0 hInf hE
    exact weighted_irrational_of_mean_target htarget b E hb hE0 hE hInf
  · intro H hH0 hH
    apply all_base_hereditary_of_binary_returns H
    intro ε hε
    obtain ⟨Q, R, M, hQ, _, hM, hsmall⟩ := htarget 2 H (by norm_num) hH0 hH ε hε 1 (by decide)
    obtain ⟨j, m, _, _, _, hsample⟩ :=
      exists_sample_lt_of_dyadicMean_lt Q R M (by omega) (displacement 2 H) ε hsmall
    exact ⟨(m + 1) * Q, Nat.mul_pos (Nat.succ_pos m) hQ, hsample⟩
end
