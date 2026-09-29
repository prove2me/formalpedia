-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.weightedScheduleError_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:50:13.96777+00:00
-- url     : https://prove2.me/submissions/5c5d323e-f53e-4e1d-8399-6e69ae9fa3a6

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
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedFiniteMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_WeightedSchedule
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_nat_sq_le_two_pow
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_samplingModulus_upper
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
# Explicit closure of the weighted observation parameters

There is no asymptotic schedule premise. With Q=L*c^H,
G=2^H and M=4Q, the entire high-GCD/geometric error is bounded by
26*2^(-H), once H >= max 4 (L+c+2). Every inequality uses natural powers.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7





theorem samplingModulus_lower (L c H : ℕ) (hL : 0 < L) (hc : 2 ≤ c) :
    2^H ≤ L*c^H := by
  have hp := Nat.pow_le_pow_left hc H
  have hmul : c^H ≤ L*c^H := by
    have hh := Nat.mul_le_mul_right (c^H) hL
    simpa using hh
  exact hp.trans hmul
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (B : ℝ) (hB2 : 2 ≤ B)
    (L c H : ℕ) (hL : 0 < L) (hc : 2 ≤ c)
    (hH4 : 4 ≤ H) (hHC : L+c+2 ≤ H) :
    weightedScheduleError B (L*c^H) (2^H) (4*(L*c^H)) ≤ 26*(1/2:ℝ)^H := by
  let Q : ℕ := L*c^H
  let G : ℕ := 2^H
  let C : ℕ := L+c
  have hQ : 0 < Q := Nat.mul_pos hL (Nat.pow_pos (lt_of_lt_of_le (by decide) hc))
  have hG : 0 < G := Nat.pow_pos (by decide)
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hden : 0 < B^G-1 := kernel_den_pos hB hG
  have hQbound : Q ≤ 2^(C*H) := samplingModulus_upper L c H (by omega)
  have hGQ : G ≤ Q := samplingModulus_lower L c H hL hc
  have hHG : H ≤ G := (show H < 2 ^ H from Nat.lt_two_pow_self).le
  have hidx : (C+2)*H ≤ G := by
    have hcH : C+2 ≤ H := hHC
    exact (Nat.mul_le_mul_right H hcH).trans (by simpa [pow_two] using nat_sq_le_two_pow hH4)
  have hQR : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hGR : (1:ℝ) ≤ G := by exact_mod_cast hG
  have hGQ1 : (1:ℝ) ≤ (G:ℝ)*(Q:ℝ) := one_le_mul_of_one_le_of_one_le hGR hQR
  have hQGQ : (Q:ℝ) ≤ (G:ℝ)*(Q:ℝ) :=
    le_mul_of_one_le_left (Nat.cast_nonneg Q) hGR
  have hnum : (G:ℝ)*((Q:ℝ)+2*((4*Q:ℕ):ℝ))+(Q:ℝ)+1 ≤
      11*(G:ℝ)*(Q:ℝ) := by push_cast; nlinarith only [hGQ1,hQGQ]
  have htwoG : (2:ℝ) ≤ (2:ℝ)^G := le_self_pow₀ (by norm_num) hG.ne'
  have hbase : (2:ℝ)^G ≤ B^G := pow_le_pow_left₀ (by norm_num) hB2 G
  have hdenLower : (2:ℝ)^G/2 ≤ B^G-1 := by linarith only [htwoG,hbase]
  have hhigh : ((G:ℝ)*((Q:ℝ)+2*((4*Q:ℕ):ℝ))+(Q:ℝ)+1)/(B^G-1) ≤
      22*((G:ℝ)*(Q:ℝ))/(2:ℝ)^G := by
    calc
      _ ≤ (11*(G:ℝ)*(Q:ℝ))/(B^G-1) := div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (11*(G:ℝ)*(Q:ℝ))/((2:ℝ)^G/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLower
      _ = _ := by ring
  have hprod : (G:ℝ)*(Q:ℝ) ≤ (2:ℝ)^((C+1)*H) := by
    have hQr : (Q:ℝ) ≤ (2:ℝ)^(C*H) := by exact_mod_cast hQbound
    have hh := mul_le_mul_of_nonneg_left hQr (Nat.cast_nonneg G)
    have heq : (G:ℝ)*(2:ℝ)^(C*H) = (2:ℝ)^((C+1)*H) := by
      dsimp [G]
      rw [Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      congr 1
      ring
    exact hh.trans_eq heq
  have hratio : (2:ℝ)^((C+1)*H)/(2:ℝ)^G ≤ (1/2:ℝ)^H := by
    rw [one_div,inv_pow,← one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have heq : (C+1)*H+H=(C+2)*H := by ring
    rw [heq]
    exact hidx
  have hsmall : ((G:ℝ)*(Q:ℝ))/(2:ℝ)^G ≤ (1/2:ℝ)^H :=
    (div_le_div_of_nonneg_right hprod (by positivity)).trans hratio
  have hfar : (1/2:ℝ)^(4*Q) ≤ (1/2:ℝ)^H :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  change ((G:ℝ)*((Q:ℝ)+2*((4*Q:ℕ):ℝ))+(Q:ℝ)+1)/(B^G-1) +
    4*(1/2:ℝ)^(4*Q) ≤ _
  have heq : 22 * ((G : ℝ) * (Q : ℝ)) / (2 : ℝ)^G =
      22 * (((G : ℝ) * (Q : ℝ)) / (2 : ℝ)^G) := by ring
  rw [heq] at hhigh
  linarith only [hhigh, hsmall, hfar]
end
