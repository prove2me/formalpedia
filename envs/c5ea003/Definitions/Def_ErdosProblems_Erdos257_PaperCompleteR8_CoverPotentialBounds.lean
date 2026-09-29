-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_CoverPotentialBounds
-- name    : ErdosProblems_Erdos257_PaperCompleteR8_CoverPotentialBounds
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T20:03:38.989982+00:00
-- url     : https://prove2.me/theorems/3a1876f8-ff84-40d5-93b1-2c4108ceb35e
-- title:
--   Cover thresholds, scales, and costs
-- statement:
--   This bundle defines a base 2^exponent(j), a geometric threshold ε·2^(−(j+1)), a scale from that threshold and exponent, and a corresponding scaled cover cost. Other retained lines in this staged file are lemmas supporting these definitions.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/CoverPotentialBounds.lean#L1-L225
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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_Displacement
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
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
# Summability and means of the ACTUAL positive-cover potentials

Compiled r8-upgrade proof candidates. Every summability condition here is
derived from PositiveCoverData and its displayed cost, before an interchange.
No extra incidence-majorisation premise or uniform positive exponent is assumed.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Reciprocal column cost is nonnegative, including conductor zero. -/
theorem positiveCover_cost_nonneg (C : PositiveCoverData) (j : ℕ) : 0 ≤ C.cost j := by
  apply tsum_nonneg
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact div_nonneg (C.coefficient_nonneg j d hd) (Nat.cast_nonneg d)

def coverBase (C : PositiveCoverData) (j : ℕ) : ℝ := (2 : ℝ) ^ C.exponent j

theorem coverBase_gt_one (C : PositiveCoverData) (j : ℕ) : 1 < coverBase C j :=
  Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
    (Or.inl ⟨by norm_num, (C.exponent_bounds j).1⟩)











/-- Dyadic threshold at paper index j+1. -/
def coverThreshold (ε : ℝ) (j : ℕ) : ℝ := ε * ((2 : ℝ) ^ (j + 1))⁻¹

theorem coverThreshold_pos {ε : ℝ} (hε : 0 < ε) (j : ℕ) : 0 < coverThreshold ε j :=
  mul_pos hε (inv_pos.mpr (pow_pos (by norm_num) _))

theorem summable_coverThreshold (ε : ℝ) : Summable (coverThreshold ε) := by
  have hgeo : Summable (fun j : ℕ => ((2 : ℝ)⁻¹) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h := hgeo.mul_left (ε * (2 : ℝ)⁻¹)
  apply h.congr
  intro j
  simp only [coverThreshold, pow_succ, mul_inv, inv_pow]
  ring

theorem tsum_coverThreshold (ε : ℝ) : (∑' j, coverThreshold ε j) = ε := by
  unfold coverThreshold
  rw [tsum_mul_left, tsum_inv_pow_succ (by norm_num : (1 : ℝ) < 2)]
  norm_num

def coverScale (C : PositiveCoverData) (ε : ℝ) (j : ℕ) : ℝ :=
  coverThreshold ε j ^ (-C.exponent j)

def coverScaledCost (C : PositiveCoverData) (ε : ℝ) (j : ℕ) : ℝ :=
  coverScale C ε j * (C.cost j / (coverBase C j - 1))

theorem coverScale_pos (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    0 < coverScale C ε j := Real.rpow_pos_of_pos (coverThreshold_pos hε j) _

theorem coverScaledCost_nonneg (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    0 ≤ coverScaledCost C ε j :=
  mul_nonneg (coverScale_pos C hε j).le
    (div_nonneg (positiveCover_cost_nonneg C j) (sub_pos.mpr (coverBase_gt_one C j)).le)

/-- The exact reindexing of the printed cost; no inverse-exponent factor is lost. -/
theorem coverScale_eq (C : PositiveCoverData) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    coverScale C ε j = ε ^ (-C.exponent j) *
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) := by
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := pow_nonneg (by norm_num) _
  have hp : (((2 : ℝ) ^ (j + 1)) ^ C.exponent j) =
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  unfold coverScale coverThreshold
  rw [Real.mul_rpow hε.le (inv_nonneg.mpr hq), Real.inv_rpow hq,
    Real.rpow_neg hq, inv_inv, hp]

/-- The displayed strengthened cost supplies all scaled test summability. -/
theorem summable_coverScaledCost (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε : ℝ} (hε : 0 < ε) :
    Summable (coverScaledCost C ε) := by
  let a : ℕ → ℝ := fun j =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) / (coverBase C j - 1)
  have ha : Summable a := hC
  have hn : ∀ j, 0 ≤ a j := by
    intro j
    exact div_nonneg (mul_nonneg (positiveCover_cost_nonneg C j)
      (Real.rpow_nonneg (by norm_num) _)) (sub_pos.mpr (coverBase_gt_one C j)).le
  have hdom : Summable (fun j => max 1 ε⁻¹ * a j) := ha.mul_left _
  apply Summable.of_nonneg_of_le (coverScaledCost_nonneg C hε) _ hdom
  intro j
  have heq : coverScaledCost C ε j = ε ^ (-C.exponent j) * a j := by
    unfold coverScaledCost
    rw [coverScale_eq C hε]
    dsimp [a]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (rpow_neg_le_max_one_inv hε (C.exponent_bounds j).1 (C.exponent_bounds j).2) (hn j)









end ErdosProblems.Erdos257.PaperCompleteR8
end


