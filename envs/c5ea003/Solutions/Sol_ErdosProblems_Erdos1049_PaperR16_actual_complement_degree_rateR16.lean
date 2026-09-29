-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR16.actual_complement_degree_rateR16
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:36:31.550736+00:00
-- url     : https://prove2.me/submissions/a66364ff-3c74-42d4-ada2-310d81d6e814

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_PaperShortCapR9
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
import Definitions.Def_ErdosProblems_Erdos1049_SourceHeightRateR14
import Definitions.Def_ErdosProblems_Erdos1049_WeightedFloorBlocksR12
import Definitions.Def_ErdosProblems_Erdos1049_G02WeightedBlocksR16
import Theorems.Thm_ErdosProblems_Erdos1049_BezoutPluckerJets_bezoutPluckerEquiv_apply
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_sqScale_nonneg
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceComplement_monic_degree
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_sourceWeight_zero_or_one
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR14_sourceLogScale_ge_one
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR14_source_n_log_squared_isLittleO
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_summatory_totient_errorR16
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_actual_weighted_totient_errorR16
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.LiminfLimsup
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace PaperR11
end PaperR11

namespace PaperR12
end PaperR12

/-! Literal thirteen-block supplier: the complement degree has quadratic rate. -/

namespace ErdosProblems.Erdos1049.PaperR16
open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000





















































lemma source_scaled_log_boundR16 (a n : ℕ) (ha : 1 ≤ a) :
    1 + Real.log (1+(a : ℝ)*(n : ℝ)) ≤ (a : ℝ) * PaperR14.sourceLogScale n := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog := Real.log_le_log (by positivity : 0 < 1+(a : ℝ)*(n : ℝ))
    (show 1+(a : ℝ)*(n : ℝ) ≤ (a : ℝ)*((n : ℝ)+2) by nlinarith)
  rw [Real.log_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (n : ℝ)+2 ≠ 0)] at hlog
  have haLog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a by linarith)
  have hnLog : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  unfold PaperR14.sourceLogScale
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hnLog]





/-- Turns the already-proved R14 logarithmic envelope into little-o. -/
lemma littleO_of_logEnvelopeR16 (f : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ᶠ n : ℕ in atTop, |f n| ≤ C*(n : ℝ)*PaperR14.sourceLogScale n^2) :
    f =o[atTop] PaperR9.sqScale := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf, PaperR14.source_n_log_squared_isLittleO.def (div_pos hε hC)] with n hn he
  have hL : 0 ≤ (n : ℝ)*PaperR14.sourceLogScale n^2 := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hL,
    abs_of_nonneg (PaperR9.sqScale_nonneg n)] at he ⊢
  calc
    |f n| ≤ C*((n : ℝ)*PaperR14.sourceLogScale n^2) := by nlinarith [hn]
    _ ≤ C*((ε/C)*PaperR9.sqScale n) := mul_le_mul_of_nonneg_left he hC.le
    _ = ε*PaperR9.sqScale n := by field_simp [hC.ne']



lemma total_totient_errorR16 (a n : ℕ) (ha : 1 ≤ a) :
    |totientPrefixR16 ((a : ℝ)*(n : ℝ)) -
      (totientConstantR16*(a : ℝ)^2)*(n : ℝ)^2| ≤
      (2*(a : ℝ)^2)*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  have h := summatory_totient_errorR16 ((a : ℝ)*(n : ℝ)) (by positivity)
  have hl := source_scaled_log_boundR16 a n ha
  have hL := PaperR14.sourceLogScale_ge_one n
  have hLs : PaperR14.sourceLogScale n ≤ PaperR14.sourceLogScale n^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(a : ℝ)*(n : ℝ) by positivity)
  have hb' := mul_le_mul_of_nonneg_left hLs (show 0 ≤ 2*(a : ℝ)^2*(n : ℝ) by positivity)
  unfold totientErrorR16 at h
  have he : totientConstantR16*((a : ℝ)*(n : ℝ))^2 =
      (totientConstantR16*(a : ℝ)^2)*(n : ℝ)^2 := by ring
  rw [he] at h
  exact h.trans (by nlinarith)

lemma actual_complement_degree_identityR16 (n : ℕ) :
    complementDegreeR16 n = totientPrefixR16 (15*(n : ℝ)) -
      (actualWeightedTotientSum n : ℝ) := by
  classical
  unfold complementDegreeR16
  rw [(sourceComplement_monic_degree n).2]
  have hf : ⌊15*(n : ℝ)⌋₊ = 15*n := by
    exact_mod_cast (Nat.floor_natCast (15 * n) : ⌊((15 * n : ℕ) : ℝ)⌋₊ = 15 * n)
  unfold totientPrefixR16 actualWeightedTotientSum
  rw [hf]
  push_cast
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro l hl
  rcases sourceWeight_zero_or_one n l with h | h <;> simp [h]

theorem actual_complement_degree_errorR16 (n : ℕ) (hn : 1 ≤ n) :
    |complementDegreeR16 n-sourceGammaR16*(n : ℝ)^2| ≤
      11377*(n : ℝ)*PaperR14.sourceLogScale n^2 := by
  rw [actual_complement_degree_identityR16]
  have ht := total_totient_errorR16 15 n (by norm_num)
  have hw := actual_weighted_totient_errorR16 n hn
  norm_num at ht
  have he : (totientPrefixR16 (15*(n : ℝ))-(actualWeightedTotientSum n : ℝ)) -
      sourceGammaR16*(n : ℝ)^2 =
      (totientPrefixR16 (15*(n : ℝ))-(totientConstantR16*225)*(n : ℝ)^2) -
        ((actualWeightedTotientSum n : ℝ)-(totientConstantR16*sourceJR16)*(n : ℝ)^2) := by
    unfold sourceGammaR16
    ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith [ht, hw])
end ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open PaperR11 PaperR12
open scoped BigOperators Topology
set_option maxHeartbeats 4000000
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR16 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution :
    QuadRateR16 complementDegreeR16 sourceGammaR16 := by
  apply littleO_of_logEnvelopeR16 _ 11377 (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa [PaperR9.sqScale] using actual_complement_degree_errorR16 n hn
