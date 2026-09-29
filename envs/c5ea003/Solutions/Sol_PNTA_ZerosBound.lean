-- Prove2me | solution 1 for PNTA.ZerosBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-12T06:13:30.090981+00:00
-- url     : https://prove2.me/submissions/d0921c46-dc85-4314-9493-4d26f6a70f5c

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Definitions.Def_PNTA_ZerosInDisc
import Theorems.Thm_PNTA_AnalyticOn_norm_le_of_norm_le_on_sphere
import Theorems.Thm_PNTA_CfAnalytic
import Theorems.Thm_PNTA_finiteSetOfZeros_mono

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical
open PNTA

private lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const

private lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]

private lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)

theorem solution {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))
