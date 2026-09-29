-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_CoverClassTransport
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_CoverClassTransport
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T20:23:08.271771+00:00
-- url     : https://prove2.me/theorems/f0a92917-78d2-46d4-9319-5be14b477763
-- title:
--   Positive-cover data transported to a log-budget cover
-- statement:
--   This bundle constructs a LogBudgetCover A from PositiveCoverData C, assuming C has summable strengthened cost and A is contained in C.host; its frame, exponent, and coefficient come from C and its weights use coverThreshold 1.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/CoverClassTransport.lean#L1-L63
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

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
import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_CoverPotentialBounds
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_OptimizedCoverBudget
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

                                                                              
                                                              
                                                                              
                                                       
  
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Every strengthened cover in the paper defines literal arbitrary-weight data. -/
def logBudgetCover_of_strengthened (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) (A : Set ℕ) (hA : A ⊆ C.host) :
    LogBudgetCover A where
  frame := C.frame
  weight := coverThreshold 1
  exponent := C.exponent
  coefficient := C.coefficient
  frame_positive := C.frame_positive
  weight_positive := fun j => coverThreshold_pos (by norm_num) j
  weight_sum := by
    simpa only [tsum_coverThreshold] using (summable_coverThreshold 1).hasSum
  exponent_bounds := C.exponent_bounds
  coefficient_nonneg := C.coefficient_nonneg
  column_summable := C.column_summable
  covers := fun a ha => hA ha
  majorises := C.majorises
  budget_summable := by
    have hs := summable_coverScaledCost C hC (by norm_num : (0 : ℝ) < 1)
    have heq : (fun j => (∑' d : ℕ, C.coefficient j d / (d : ℝ)) /
        (coverThreshold 1 j ^ C.exponent j) / ((2 : ℝ) ^ C.exponent j - 1)) =
        coverScaledCost C 1 := by
      funext j
      unfold coverScaledCost coverScale PositiveCoverData.cost coverBase
      rw [Real.rpow_neg (coverThreshold_pos (by norm_num : (0 : ℝ) < 1) j).le]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    exact hs







end ErdosProblems.Erdos257.PaperCompleteR8
end


