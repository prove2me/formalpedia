-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.progressionMean_kernel_le_profile
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:25:24.005381+00:00
-- url     : https://prove2.me/submissions/ee88ff2c-caf3-49a5-95e4-1fd166ec230d

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedPrimeProfile
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteEstimates
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_profileWeight_nonneg
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_geom_ratio_antitone
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_progressionMean_kernel_le_gcdMean_add_error
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
# Finite weighted estimates with an explicit observation window

The high-GCD remainder is charged against a dyadic harmonic
bound, not against the cardinality of an unbounded conductor support.
The future-conductor contribution is bounded geometrically before any
infinite interchange. All constants here are deliberately non-sharp.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB : 1 < B)
    (Q G T : ℕ) (hQ : 0 < Q) (hG : 0 < G) (hT : 0 < T)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h) (a : ℕ) (ha : 0 < a) :
    progressionMean Q T (kernelWeight B a) ≤
      profileWeight B h a + 1/((T:ℝ)*(B^h a-1)) +
      (G:ℝ)/((a:ℝ)*(B^G-1)) + 1/((T:ℝ)*(B^G-1)) := by
  let g := Nat.gcd Q a
  have hg : 0 < g := Nat.gcd_pos_of_pos_left a hQ
  have hbase := progressionMean_kernel_le_gcdMean_add_error B hB Q a T hQ ha hT
  have hGD : 0 < B^G-1 := kernel_den_pos hB hG
  obtain ⟨hh, hgood | hbad⟩ := hprof a ha
  · have hle : h a ≤ g := Nat.le_of_dvd hg hgood
    have hr := geom_ratio_antitone B hB (h a) g hh hle
    have hmain : (g:ℝ)/((a:ℝ)*(B^g-1)) ≤ profileWeight B h a := by
      calc
        (g:ℝ)/((a:ℝ)*(B^g-1)) = ((g:ℝ)/(B^g-1))/(a:ℝ) := by simp only [div_div, mul_comm]
        _ ≤ ((h a:ℝ)/(B^h a-1))/(a:ℝ) :=
          div_le_div_of_nonneg_right hr (Nat.cast_nonneg a)
        _ = profileWeight B h a := by simp only [profileWeight, div_div, mul_comm]
    have hden : B^h a-1 ≤ B^g-1 := sub_le_sub_right (pow_le_pow_right₀ hB.le hle) 1
    have herr : 1/((T:ℝ)*(B^g-1)) ≤ 1/((T:ℝ)*(B^h a-1)) := by
      apply one_div_le_one_div_of_le
      · exact mul_pos (by exact_mod_cast hT) (kernel_den_pos hB hh)
      · exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg T)
    have h0 : 0 ≤ (G:ℝ)/((a:ℝ)*(B^G-1)) :=
      div_nonneg (Nat.cast_nonneg G) (mul_nonneg (Nat.cast_nonneg a) hGD.le)
    have h1 : 0 ≤ 1/((T:ℝ)*(B^G-1)) :=
      one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg T) hGD.le)
    linarith only [hbase, hmain, herr, h0, h1]
  · have hr := geom_ratio_antitone B hB G g hG hbad
    have hmain : (g:ℝ)/((a:ℝ)*(B^g-1)) ≤ (G:ℝ)/((a:ℝ)*(B^G-1)) := by
      have hb := div_le_div_of_nonneg_right hr (Nat.cast_nonneg a)
      simpa only [div_div, mul_comm] using hb
    have hden : B^G-1 ≤ B^g-1 := sub_le_sub_right (pow_le_pow_right₀ hB.le hbad) 1
    have herr : 1/((T:ℝ)*(B^g-1)) ≤ 1/((T:ℝ)*(B^G-1)) := by
      apply one_div_le_one_div_of_le
      · exact mul_pos (by exact_mod_cast hT) (kernel_den_pos hB hG)
      · exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg T)
    have h0 : 0 ≤ profileWeight B h a := profileWeight_nonneg B hB h a hh
    have h1 : 0 ≤ 1/((T:ℝ)*(B^h a-1)) := by
      exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg T) (kernel_den_pos hB hh).le)
    linarith only [hbase, hmain, herr, h0, h1]
end
