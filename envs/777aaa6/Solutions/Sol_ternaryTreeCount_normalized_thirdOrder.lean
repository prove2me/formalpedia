-- Prove2me | solution 1 for ternaryTreeCount_normalized_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:40:44.476753+00:00
-- url     : https://prove2.me/submissions/e08bd624-b8f3-4860-b40d-adf888349e44

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffExplicit
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_ModelCoeffThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Explicit first-order model coefficient estimate

This file packages the exact Gamma-ratio route for the standard model
coefficient

`[z^n] (1 - z)^(-α) = Ring.choose (α + n - 1) n`.

The algebraic coefficient/Gamma identity is proved here.  The first-order
Gamma-ratio estimate is proved below from Bohr-Mollerup log-convexity.
-/

open Filter Asymptotics
open scoped BigOperators

noncomputable section

private lemma logGamma_add_one {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) = (Real.log ∘ Real.Gamma) y + Real.log y := by
  dsimp [Function.comp_def]
  rw [Real.Gamma_add_one hy.ne']
  rw [Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

private lemma logGamma_unit_upper
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.log (Real.Gamma ((n : ℝ) + β))
      ≤ Real.log (Real.Gamma (n : ℝ)) + β * Real.log (n : ℝ) := by
  simpa [Function.comp_def] using
    Real.BohrMollerup.f_add_nat_le
      (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma
      (fun {y} hy => logGamma_add_one hy)
      hn hβ0 hβ1

private lemma logGamma_unit_lower
    {β : ℝ} (hβ0 : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.Gamma (n : ℝ)) + β * Real.log ((n : ℝ) - 1)
      ≤ Real.log (Real.Gamma ((n : ℝ) + β)) := by
  simpa [Function.comp_def] using
    Real.BohrMollerup.f_add_nat_ge
      (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma
      (fun {y} hy => logGamma_add_one hy)
      hn hβ0

private lemma gamma_unit_upper
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.Gamma ((n : ℝ) + β)
      ≤ Real.Gamma (n : ℝ) * (n : ℝ) ^ β := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hΓnb_pos : 0 < Real.Gamma ((n : ℝ) + β) := Real.Gamma_pos_of_pos (by positivity)
  have hrpow_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  rw [← Real.log_le_log_iff hΓnb_pos (mul_pos hΓn_pos hrpow_pos)]
  calc
    Real.log (Real.Gamma ((n : ℝ) + β))
        ≤ Real.log (Real.Gamma (n : ℝ)) + β * Real.log (n : ℝ) :=
          logGamma_unit_upper hβ0 hβ1 hn
    _ = Real.log (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) := by
          rw [Real.log_mul hΓn_pos.ne' hrpow_pos.ne', Real.log_rpow hnpos]

private lemma gamma_unit_lower
    {β : ℝ} (hβ0 : 0 < β)
    {n : ℕ} (hn : 2 ≤ n) :
    Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β
      ≤ Real.Gamma ((n : ℝ) + β) := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hnm1pos : 0 < (n : ℝ) - 1 := by linarith
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hΓnb_pos : 0 < Real.Gamma ((n : ℝ) + β) := Real.Gamma_pos_of_pos (by positivity)
  have hrpow_pos : 0 < ((n : ℝ) - 1) ^ β := Real.rpow_pos_of_pos hnm1pos β
  rw [← Real.log_le_log_iff (mul_pos hΓn_pos hrpow_pos) hΓnb_pos]
  calc
    Real.log (Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β)
        = Real.log (Real.Gamma (n : ℝ)) + β * Real.log ((n : ℝ) - 1) := by
          rw [Real.log_mul hΓn_pos.ne' hrpow_pos.ne', Real.log_rpow hnm1pos]
    _ ≤ Real.log (Real.Gamma ((n : ℝ) + β)) := logGamma_unit_lower hβ0 hn

private lemma gamma_unit_norm_eq {β : ℝ} {n : ℕ} (hn : 0 < (n : ℝ)) :
    Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1) / ((n : ℝ) ^ (β - 1)) =
      Real.Gamma ((n : ℝ) + β) / (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) := by
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hn
  have hpow_pos : 0 < (n : ℝ) ^ (β - 1) := Real.rpow_pos_of_pos hn (β - 1)
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn β
  have hΓn1 : Real.Gamma ((n : ℝ) + 1) = (n : ℝ) * Real.Gamma (n : ℝ) :=
    Real.Gamma_add_one hn.ne'
  have hpow : (n : ℝ) * (n : ℝ) ^ (β - 1) = (n : ℝ) ^ β := by
    calc
      (n : ℝ) * (n : ℝ) ^ (β - 1) =
          (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (β - 1) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (β - 1)) := by rw [Real.rpow_add hn]
      _ = (n : ℝ) ^ β := by ring_nf
  rw [hΓn1]
  field_simp [hΓn_pos.ne', hn.ne', hpow_pos.ne', hpowβ_pos.ne']
  calc
    Real.Gamma ((n : ℝ) + β) * (n : ℝ) ^ β =
        Real.Gamma ((n : ℝ) + β) * ((n : ℝ) * (n : ℝ) ^ (β - 1)) := by
          rw [hpow]
    _ = (n : ℝ) * Real.Gamma ((n : ℝ) + β) * (n : ℝ) ^ (β - 1) := by ring

private lemma lower_mul_eq {β : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (1 - (1 : ℝ) / (n : ℝ)) ^ β *
        (Real.Gamma (n : ℝ) * (n : ℝ) ^ β) =
      Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hnm1_nonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
  have hdiv : ((n : ℝ) - 1) / (n : ℝ) = 1 - (1 : ℝ) / (n : ℝ) := by
    field_simp [hnpos.ne']
  have hdivpow : (1 - (1 : ℝ) / (n : ℝ)) ^ β =
      ((n : ℝ) - 1) ^ β / (n : ℝ) ^ β := by
    rw [← hdiv]
    rw [Real.div_rpow hnm1_nonneg hn_nonneg]
  rw [hdivpow]
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  field_simp [hpowβ_pos.ne']

private lemma gamma_unit_norm_between
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    (1 - (1 : ℝ) / (n : ℝ)) ^ β
      ≤ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1))
      ∧ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1)) ≤ 1 := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hΓn_pos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hpowβ_pos : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hnpos β
  have hden_pos : 0 < Real.Gamma (n : ℝ) * (n : ℝ) ^ β := mul_pos hΓn_pos hpowβ_pos
  have hR_eq := gamma_unit_norm_eq (β := β) (n := n) hnpos
  constructor
  · rw [hR_eq, le_div_iff₀ hden_pos]
    calc
      (1 - (1 : ℝ) / (n : ℝ)) ^ β * (Real.Gamma (n : ℝ) * (n : ℝ) ^ β)
          = Real.Gamma (n : ℝ) * ((n : ℝ) - 1) ^ β := lower_mul_eq (β := β) hn
      _ ≤ Real.Gamma ((n : ℝ) + β) := gamma_unit_lower hβ0 hn
  · rw [hR_eq, div_le_one hden_pos]
    exact gamma_unit_upper hβ0 hβ1 (Nat.ne_of_gt hnpos_nat)

private lemma one_sub_inv_le_rpow
    {β : ℝ} (hβ1 : β ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) :
    1 - (1 : ℝ) / (n : ℝ)
      ≤ (1 - (1 : ℝ) / (n : ℝ)) ^ β := by
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1_nat : (1 : ℕ) < n := Nat.lt_of_succ_le hn
  have hn1r : (1 : ℝ) < n := by exact_mod_cast hn1_nat
  have hdivlt : (1 : ℝ) / (n : ℝ) < 1 := (div_lt_one hnpos).mpr hn1r
  have hdiv_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  have hx0 : 0 < 1 - (1 : ℝ) / (n : ℝ) := by linarith
  have hx1 : 1 - (1 : ℝ) / (n : ℝ) ≤ 1 := by linarith
  calc
    1 - (1 : ℝ) / (n : ℝ) =
        (1 - (1 : ℝ) / (n : ℝ)) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
    _ ≤ (1 - (1 : ℝ) / (n : ℝ)) ^ β :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hβ1

private theorem gamma_ratio_unit_rel_error_isBigO
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
        / ((n : ℝ) ^ (β - 1)) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have hbetween := gamma_unit_norm_between hβ0 hβ1 hn
  have hlow : 1 - (1 : ℝ) / (n : ℝ)
      ≤ Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
          / ((n : ℝ) ^ (β - 1)) :=
    (one_sub_inv_le_rpow hβ1 hn).trans hbetween.1
  have hupper := hbetween.2
  let R : ℝ :=
    Real.Gamma ((n : ℝ) + β) / Real.Gamma ((n : ℝ) + 1)
      / ((n : ℝ) ^ (β - 1))
  have hnonpos : R - 1 ≤ 0 := by simpa [R] using sub_nonpos.mpr hupper
  have hdist : ‖R - 1‖ = 1 - R := by
    rw [Real.norm_of_nonpos hnonpos]
    ring
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  have hle_inv : 1 - R ≤ (n : ℝ)⁻¹ := by
    have hlowR : 1 - (1 : ℝ) / (n : ℝ) ≤ R := by simpa [R] using hlow
    have hlowR' : 1 - (n : ℝ)⁻¹ ≤ R := by simpa [one_div] using hlowR
    linarith
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (-(1 : ℝ)) := by positivity
  calc
    ‖R - 1‖ = 1 - R := hdist
    _ ≤ (n : ℝ) ^ (-(1 : ℝ)) := by simpa [hpow_inv] using hle_inv
    _ = 1 * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
          rw [Real.norm_of_nonneg hpow_nonneg]
          ring

private lemma gammaShiftNorm_succ_eq {β : ℝ} (hβ0 : 0 < β)
    {m n : ℕ} (hn : 0 < n) :
    gammaShiftNorm β (m + 1) n =
      gammaShiftNorm β m n * (1 + (β + (m : ℝ)) / (n : ℝ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hΓden_pos : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hpow_m_pos : 0 < (n : ℝ) ^ (β + (m : ℝ) - 1) :=
    Real.rpow_pos_of_pos hnpos _
  have hs_pos : 0 < (n : ℝ) + β + (m : ℝ) := by positivity
  have hΓsucc : Real.Gamma ((n : ℝ) + β + (m + 1 : ℕ)) =
      ((n : ℝ) + β + (m : ℝ)) * Real.Gamma ((n : ℝ) + β + m) := by
    calc
      Real.Gamma ((n : ℝ) + β + (m + 1 : ℕ))
          = Real.Gamma (((n : ℝ) + β + (m : ℝ)) + 1) := by
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + β + (m : ℝ)) * Real.Gamma ((n : ℝ) + β + m) :=
          Real.Gamma_add_one hs_pos.ne'
  have hpow_succ : (n : ℝ) ^ (β + ((m + 1 : ℕ) : ℝ) - 1) =
      (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) := by
    calc
      (n : ℝ) ^ (β + ((m + 1 : ℕ) : ℝ) - 1)
          = (n : ℝ) ^ ((β + (m : ℝ) - 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add]
              ring
      _ = (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (β + (m : ℝ) - 1) * (n : ℝ) := by rw [Real.rpow_one]
  unfold gammaShiftNorm
  rw [hΓsucc, hpow_succ]
  field_simp [hΓden_pos.ne', hpow_m_pos.ne', hnpos.ne']
  ring

private lemma const_div_natCast_isBigO_rpow_neg_one (c : ℝ) :
    (fun n : ℕ => c / (n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  refine IsBigO.of_bound ‖c‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  calc
    ‖c / (n : ℝ)‖ = ‖c‖ * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := by
      rw [div_eq_mul_inv, norm_mul, hpow_inv]
    _ ≤ ‖c‖ * ‖(n : ℝ) ^ (-(1 : ℝ))‖ := le_rfl

private lemma inv_natCast_rpow_neg_one_isBigO_one :
    (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) =O[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow_inv : (n : ℝ) ^ (-(1 : ℝ)) = ((n : ℝ)⁻¹) := by
    rw [Real.rpow_neg (le_of_lt hnpos), Real.rpow_one]
  have hinv_le : ((n : ℝ)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hinv_nonneg : 0 ≤ ((n : ℝ)⁻¹) := by positivity
  rw [hpow_inv, Real.norm_of_nonneg hinv_nonneg, Real.norm_of_nonneg zero_le_one]
  simpa using hinv_le

private lemma one_add_const_div_isBigO_one (c : ℝ) :
    (fun n : ℕ => 1 + c / (n : ℝ)) =O[atTop]
      (fun _n : ℕ => (1 : ℝ)) := by
  have hconst : (fun _n : ℕ => (1 : ℝ)) =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    isBigO_refl _ _
  have hcdiv := (const_div_natCast_isBigO_rpow_neg_one c).trans
    inv_natCast_rpow_neg_one_isBigO_one
  exact hconst.add hcdiv

private theorem gamma_ratio_shift_rel_error_isBigO
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    (fun n : ℕ => gammaShiftNorm β m n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
  induction m with
  | zero =>
      simpa [gammaShiftNorm] using gamma_ratio_unit_rel_error_isBigO hβ0 hβ1
  | succ m ih =>
      let c : ℝ := β + (m : ℝ)
      have hfactor : (fun n : ℕ => 1 + c / (n : ℝ)) =O[atTop]
          (fun _n : ℕ => (1 : ℝ)) := one_add_const_div_isBigO_one c
      have hcdiv : (fun n : ℕ => c / (n : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) :=
        const_div_natCast_isBigO_rpow_neg_one c
      have hprod0 := ih.mul hfactor
      have hprod : (fun n : ℕ => (gammaShiftNorm β m n - 1) * (1 + c / (n : ℝ)))
          =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
        exact hprod0.congr_right (fun n => by ring)
      have hsum := hprod.add hcdiv
      have heq : (fun n : ℕ => gammaShiftNorm β (m + 1) n - 1) =ᶠ[atTop]
          (fun n : ℕ => (gammaShiftNorm β m n - 1) *
              (1 + c / (n : ℝ)) + c / (n : ℝ)) := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
        rw [gammaShiftNorm_succ_eq hβ0 hnpos]
        dsimp [c]
        ring
      exact heq.trans_isBigO hsum

private theorem gamma_ratio_shift_firstOrder
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (m : ℕ) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1)
        - (n : ℝ) ^ (β + (m : ℝ) - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 2)) := by
  have hrel := gamma_ratio_shift_rel_error_isBigO hβ0 hβ1 m
  have hp : (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 1)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 1)) := isBigO_refl _ _
  have hmul : (fun n : ℕ =>
        (n : ℝ) ^ (β + (m : ℝ) - 1) * (gammaShiftNorm β m n - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + (m : ℝ) - 2)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := β + (m : ℝ) - 1) (b := -(1 : ℝ)) (c := β + (m : ℝ) - 2)
      hp hrel (by linarith)
  have heq : (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + β + m) / Real.Gamma ((n : ℝ) + 1)
        - (n : ℝ) ^ (β + (m : ℝ) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        (n : ℝ) ^ (β + (m : ℝ) - 1) * (gammaShiftNorm β m n - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hp_pos : 0 < (n : ℝ) ^ (β + (m : ℝ) - 1) := Real.rpow_pos_of_pos hnpos _
    unfold gammaShiftNorm
    field_simp [hp_pos.ne']
  exact heq.trans_isBigO hmul

private theorem gamma_ratio_first_order_of_decomp
    {α β : ℝ} (m : ℕ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hα : α = β + (m : ℝ)) :
    (fun n : ℕ => Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  subst α
  simpa [add_assoc, add_comm, add_left_comm] using
    gamma_ratio_shift_firstOrder hβ0 hβ1 m

private theorem gamma_ratio_decomp {α : ℝ} (hα : 0 < α) :
    ∃ (β : ℝ) (m : ℕ), 0 < β ∧ β ≤ 1 ∧ α = β + (m : ℝ) := by
  let m : ℕ := Nat.ceil α - 1
  let β : ℝ := α - (m : ℝ)
  have hceil_pos : 0 < Nat.ceil α := Nat.ceil_pos.mpr hα
  have hm_lt_ceil : m < Nat.ceil α := by
    dsimp [m]
    exact Nat.sub_one_lt (Nat.ne_of_gt hceil_pos)
  have hm_lt_alpha : (m : ℝ) < α := (Nat.lt_ceil).mp hm_lt_ceil
  have hβ0 : 0 < β := by
    dsimp [β]
    linarith
  have hceil_le_alpha : α ≤ (Nat.ceil α : ℝ) := (Nat.ceil_le).mp (le_refl (Nat.ceil α))
  have hm_succ : m + 1 = Nat.ceil α := by
    dsimp [m]
    exact Nat.succ_pred_eq_of_pos hceil_pos
  have hm1_cast : (m : ℝ) + 1 = (Nat.ceil α : ℝ) := by
    rw [← hm_succ]
    norm_num
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    linarith
  refine ⟨β, m, hβ0, hβ1, ?_⟩
  dsimp [β]
  ring

theorem gamma_ratio_first_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => Real.Gamma (n + α) / Real.Gamma (n + 1) - (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 2)) := by
  rcases gamma_ratio_decomp hα with ⟨β, m, hβ0, hβ1, hαeq⟩
  exact gamma_ratio_first_order_of_decomp m hβ0 hβ1 hαeq

end
end

section
/-!
# Third-order model coefficient estimate

This file proves the third coefficient in the Gamma-ratio/model-coefficient
expansion by the recurrence bootstrap route.  It does not use Stirling or
digamma asymptotics.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

private lemma choose_neg_two (α : ℝ) :
    Ring.choose (-α) 2 = α * (α + 1) / 2 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 2
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma choose_neg_three (α : ℝ) :
    Ring.choose (-α) 3 = -α * (α + 1) * (α + 2) / 6 := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (-α : ℝ) 3
  norm_num [descPochhammer, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_C, Polynomial.smeval_natCast] at h
  nlinarith

private lemma binomial_partialSum_three (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 3 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two]
  ring_nf

private lemma binomial_partialSum_four (α x : ℝ) :
    (binomialSeries ℝ (-α)).partialSum 4 x =
      1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
        (α * (α + 1) * (α + 2) / 6) * x ^ 3 := by
  simp [FormalMultilinearSeries.partialSum, binomialSeries, Finset.sum_range_succ,
    choose_neg_two, choose_neg_three]
  ring_nf

private lemma rpow_neg_sub_quadratic_isBigO (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) - (1 - α * x + (α * (α + 1) / 2) * x ^ 2))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 3
  exact h.congr_left fun x => by
    rw [binomial_partialSum_three]
    simp

private lemma rpow_neg_sub_cubic_isBigO (α : ℝ) :
    (fun x : ℝ =>
      (1 + x) ^ (-α) -
        (1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
          (α * (α + 1) * (α + 2) / 6) * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -α)).isBigO_sub_partialSum_pow 4
  exact h.congr_left fun x => by
    rw [binomial_partialSum_four]
    simp

private lemma linear_near_zero_isBigO_one (α : ℝ) :
    (fun x : ℝ => 1 + α * x) =O[𝓝 0] (fun _x : ℝ => (1 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 1 + α * x) (𝓝 0) (𝓝 ((fun x : ℝ => 1 + α * x) 0)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  simpa using ht.isBigO_one ℝ

private lemma const_mul_cubic_isBigO_norm_cubic (a : ℝ) :
    (fun x : ℝ => a * x ^ 3) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 3‖ = ‖a‖ * ‖x‖ ^ 3 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 3‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 3)]

private lemma const_mul_quartic_isBigO_norm_quartic (a : ℝ) :
    (fun x : ℝ => a * x ^ 4) =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  refine IsBigO.of_bound ‖a‖ ?_
  filter_upwards with x
  calc
    ‖a * x ^ 4‖ = ‖a‖ * ‖x‖ ^ 4 := by
      rw [norm_mul, norm_pow]
    _ ≤ ‖a‖ * ‖‖x‖ ^ 4‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 4)]

private lemma gammaStep_local_at_zero (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) - 1 + c1 α * x ^ 2)
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
  let q : ℝ → ℝ := fun x => 1 - α * x + (α * (α + 1) / 2) * x ^ 2
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    simpa [q] using rpow_neg_sub_quadratic_isBigO α
  have hlin := linear_near_zero_isBigO_one α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hcubic :
      (fun x : ℝ => (α ^ 2 * (α + 1) / 2) * x ^ 3)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 3) :=
    const_mul_cubic_isBigO_norm_cubic _
  have hsum := hprod.add hcubic
  exact hsum.congr_left fun x => by
    dsimp [q, c1]
    ring_nf

private lemma gammaStep_local_third (α : ℝ) :
    (fun x : ℝ =>
      (1 + α * x) * (1 + x) ^ (-α) -
        (1 - c1 α * x ^ 2 + d3 α * x ^ 3))
      =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
  let q : ℝ → ℝ := fun x =>
    1 - α * x + (α * (α + 1) / 2) * x ^ 2 -
      (α * (α + 1) * (α + 2) / 6) * x ^ 3
  have hrem :
      (fun x : ℝ => (1 + x) ^ (-α) - q x)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
    simpa [q] using rpow_neg_sub_cubic_isBigO α
  have hlin := linear_near_zero_isBigO_one α
  have hprod0 := hlin.mul hrem
  have hprod :
      (fun x : ℝ => (1 + α * x) * ((1 + x) ^ (-α) - q x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) := by
    refine hprod0.congr_left ?_ |>.congr_right ?_
    · intro x
      ring_nf
    · intro x
      simp
  have hquartic :
      (fun x : ℝ => (-(α ^ 2 * (α + 1) * (α + 2) / 6)) * x ^ 4)
        =O[𝓝 0] (fun x : ℝ => ‖x‖ ^ 4) :=
    const_mul_quartic_isBigO_norm_quartic _
  have hsum := hprod.add hquartic
  exact hsum.congr_left fun x => by
    dsimp [q, c1, d3]
    ring_nf

private lemma inv_norm_cube_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 3 = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_norm_four_eq (n : ℕ) :
    ‖((n : ℝ)⁻¹)‖ ^ 4 = ((n : ℝ)⁻¹) ^ 4 := by
  rw [Real.norm_of_nonneg]
  positivity

private lemma inv_cube_isBigO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 2)]

private lemma gammaStep_sub_isBigO_inv_cube (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hcomp :=
    (gammaStep_local_at_zero α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_cube_eq n

private lemma gammaStep_sub_third_isBigO_inv_four (α : ℝ) :
    (fun n : ℕ =>
      gammaStep α n -
        (1 - c1 α * ((n : ℝ)⁻¹) ^ 2 +
          d3 α * ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  have hcomp :=
    (gammaStep_local_third α).comp_tendsto
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine hcomp.congr_left ?_ |>.congr_right ?_
  · intro n
    simp [gammaStep]
  · intro n
    exact inv_norm_four_eq n

private lemma const_mul_inv_sq_isBigO_inv_sq (a : ℝ) :
    (fun n : ℕ => a * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop).const_mul_left a

private lemma gammaStep_sub_one_isBigO_inv_sq (α : ℝ) :
    (fun n : ℕ => gammaStep α n - 1)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have h3 := (gammaStep_sub_isBigO_inv_cube α).trans inv_cube_isBigO_inv_sq
  have hc := const_mul_inv_sq_isBigO_inv_sq (-(c1 α))
  have hsum := h3.add hc
  refine hsum.congr_left ?_
  intro n
  ring_nf

private lemma gammaRatioNorm_succ
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop,
      gammaRatioNorm α (n + 1) = gammaRatioNorm α n * gammaStep α n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hbase_pos : 0 < 1 + (n : ℝ)⁻¹ := by positivity
  have hs_pos : 0 < (n : ℝ) + α := by positivity
  have hΓnum : Real.Gamma (((n + 1 : ℕ) : ℝ) + α) =
      ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + α)
          = Real.Gamma (((n : ℝ) + α) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + α) * Real.Gamma ((n : ℝ) + α) :=
          Real.Gamma_add_one hs_pos.ne'
  have hΓden : Real.Gamma (((n + 1 : ℕ) : ℝ) + 1) =
      ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
    calc
      Real.Gamma (((n + 1 : ℕ) : ℝ) + 1)
          = Real.Gamma (((n : ℝ) + 1) + 1) := by
              congr 1
              norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
      _ = ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
          exact Real.Gamma_add_one (by positivity : (n : ℝ) + 1 ≠ 0)
  have hnadd : (n : ℝ) + 1 = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    field_simp [hnne]
  have hn1eq : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
    rw [Nat.cast_add, Nat.cast_one, hnadd]
  have hpow : (((n + 1 : ℕ) : ℝ)) ^ (α - 1) =
      ((n : ℝ) ^ (α - 1)) * (1 + (n : ℝ)⁻¹) ^ (α - 1) := by
    rw [hn1eq]
    rw [Real.mul_rpow (le_of_lt hnpos) (le_of_lt hbase_pos)]
  have hbase_alpha : (1 + (n : ℝ)⁻¹) ^ α =
      (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
    calc
      (1 + (n : ℝ)⁻¹) ^ α
          = (1 + (n : ℝ)⁻¹) ^ ((α - 1) + 1) := by ring_nf
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) *
            (1 + (n : ℝ)⁻¹) ^ (1 : ℝ) := by
          rw [Real.rpow_add hbase_pos]
      _ = (1 + (n : ℝ)⁻¹) ^ (α - 1) * (1 + (n : ℝ)⁻¹) := by
          rw [Real.rpow_one]
  have hΓnum_ne : Real.Gamma ((n : ℝ) + α) ≠ 0 :=
    (Real.Gamma_pos_of_pos hs_pos).ne'
  have hΓden_ne : Real.Gamma ((n : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
  have hpow_n_ne : ((n : ℝ) ^ (α - 1)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hbase_pow_ne : (1 + (n : ℝ)⁻¹) ^ (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  have hbase_alpha_ne : (1 + (n : ℝ)⁻¹) ^ α ≠ 0 :=
    (Real.rpow_pos_of_pos hbase_pos _).ne'
  unfold gammaRatioNorm gammaStep
  rw [hΓnum, hΓden, hpow, hnadd, Real.rpow_neg (le_of_lt hbase_pos), hbase_alpha]
  field_simp [hΓnum_ne, hΓden_ne, hpow_n_ne, hbase_pow_ne, hbase_alpha_ne,
    hnne, hbase_pos.ne']

private lemma rpow_neg_one_eq_inv_nat (n : ℕ) :
    (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_one]

private lemma rpow_neg_three_eq_inv_cube_nat (n : ℕ) :
    (n : ℝ) ^ (-(3 : ℝ)) = ((n : ℝ)⁻¹) ^ 3 := by
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

private lemma gammaRatioNorm_sub_one_isBigO_inv
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  set_option backward.isDefEq.respectTransparency false in
    have hA1 := gamma_ratio_first_order hα
    have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
    have hmul :
        (fun n : ℕ =>
          (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
            (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α))
          =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
      exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := α - 2) (b := 1 - α) (c := -(1 : ℝ)) hA1 hp (by linarith)
    have heq : (fun n : ℕ => gammaRatioNorm α n - 1) =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
            (n : ℝ) ^ (α - 1)) * (n : ℝ) ^ (1 - α)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
      have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
      have hpow_inv : (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (α - 1))⁻¹ := by
        rw [← Real.rpow_neg (le_of_lt hnpos)]
        congr 1
        ring_nf
      unfold gammaRatioNorm
      rw [hpow_inv]
      field_simp [hpow_ne]
    exact (heq.trans_isBigO hmul).congr_right fun n => by
      rw [rpow_neg_one_eq_inv_nat]

private lemma tail_inv_sq_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) ≤
      2 / ((N : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hreindex : (∑ i ∈ Finset.range n,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)
      = ∑ k ∈ Finset.Ico (N + 1) (N + 1 + n), 1 / ((k : ℝ)) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : N + 1 + n - (N + 1) = n := by omega
    rw [hsub]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [show i + N + 1 = N + 1 + i from by omega]
  rw [hreindex]
  have hIco : Finset.Ico (N + 1) (N + 1 + n) = Finset.Ioo N (N + 1 + n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hIco]
  have hbound := sum_Ioo_inv_sq_le (α := ℝ) N (N + 1 + n)
  simp only [one_div]
  exact hbound

private lemma tail_inv_cube_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) ≤
      2 / ((N : ℝ) + 1) ^ 2 := by
  have hcube_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hsquare_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hsquare_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hinv_le hsquare_nonneg
  have hle := hcube_summ.tsum_le_tsum hterm hsquare_summ
  have hsquare_bound := tail_inv_sq_shift N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 2) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hsquare_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 2 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma tail_inv_four_shift (N : ℕ) :
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4) ≤
      2 / ((N : ℝ) + 1) ^ 3 := by
  have hfour_summ : Summable
      (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
    have hshift := (summable_nat_add_iff (N + 1)).mpr h
    refine hshift.congr fun i => ?_
    have he : i + (N + 1) = i + N + 1 := by omega
    rw [he]
  have hcube_summ : Summable
      (fun i : ℕ => (1 / ((N : ℝ) + 1)) *
        (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3)) := by
    have h : Summable (fun i : ℕ => 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
      have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
      refine hshift.congr fun i => ?_
      have he : i + (N + 1) = i + N + 1 := by omega
      rw [he]
    exact h.mul_left _
  have hterm : ∀ i : ℕ,
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4 ≤
        (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hNpos : 0 < (N : ℝ) + 1 := by positivity
    have hkpos : 0 < (((i + N + 1 : ℕ)) : ℝ) := by positivity
    have hle_nat : N + 1 ≤ i + N + 1 := by omega
    have hle : (N : ℝ) + 1 ≤ ((i + N + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    have hinv_le : 1 / (((i + N + 1 : ℕ)) : ℝ) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos hle
    have hcube_nonneg : 0 ≤ 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3 := by positivity
    calc
      1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4
          = (1 / (((i + N + 1 : ℕ)) : ℝ)) *
              (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
              field_simp [hkpos.ne']
      _ ≤ (1 / ((N : ℝ) + 1)) *
            (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right hinv_le hcube_nonneg
  have hle := hfour_summ.tsum_le_tsum hterm hcube_summ
  have hcube_bound := tail_inv_cube_shift N
  calc
    (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 4)
        ≤ ∑' i : ℕ, (1 / ((N : ℝ) + 1)) *
          (1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := hle
    _ = (1 / ((N : ℝ) + 1)) *
          (∑' i : ℕ, 1 / (((i + N + 1 : ℕ)) : ℝ) ^ 3) := by
          rw [tsum_mul_left]
    _ ≤ (1 / ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcube_bound (by positivity)
    _ = 2 / ((N : ℝ) + 1) ^ 3 := by
          field_simp [(by positivity : (N : ℝ) + 1 ≠ 0)]

private lemma summable_of_isBigO_inv_cube {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 3)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 3‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 3 := by rw [hnorm]

private lemma summable_of_isBigO_inv_four {d : ℕ → ℝ}
    (hd : d =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)) :
    Summable d := by
  rcases hd.exists_pos with ⟨C, hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * (((n : ℝ)⁻¹) ^ 4)) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
      have h' : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
      exact h'.congr fun n => by
        rw [one_div, inv_pow]
    exact h.mul_left C
  refine Summable.of_norm_bounded_eventually hmajor ?_
  have hb := hC.bound
  rw [eventually_atTop] at hb
  rcases hb with ⟨N, hN⟩
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have hnorm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg hnonneg]
  calc
    ‖d n‖ ≤ C * ‖((n : ℝ)⁻¹) ^ 4‖ := hN n hnN
    _ = C * ((n : ℝ)⁻¹) ^ 4 := by rw [hnorm]

private lemma sum_range_succDiff (u : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n))) =
      u (n + m) - u n := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : m + n + 1 = n + (m + 1) := by omega
      rw [h1]
      ring_nf

private lemma eq_neg_tsum_succDiff {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hd_summ : Summable (fun n : ℕ => u (n + 1) - u n)) (n : ℕ) :
    u n = -∑' i : ℕ, (u (i + n + 1) - u (i + n)) := by
  set_option backward.isDefEq.respectTransparency false in
    let d : ℕ → ℝ := fun k => u (k + 1) - u k
    have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
      (summable_nat_add_iff n).mpr hd_summ
    have hleft := htail_summ.tendsto_sum_tsum_nat
    have hleft' :
        Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (u (i + n + 1) - u (i + n)))
          atTop (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
      refine hleft.congr' ?_
      filter_upwards with m
      apply Finset.sum_congr rfl
      intro i _hi
      dsimp [d]
    have hright :
        Tendsto (fun m : ℕ => u (n + m) - u n) atTop (𝓝 (0 - u n)) := by
      have hcomp : Tendsto (fun m : ℕ => u (m + n)) atTop (𝓝 0) :=
        hu.comp (tendsto_add_atTop_nat n)
      have hcomp' : Tendsto (fun m : ℕ => u (n + m)) atTop (𝓝 0) := by
        refine hcomp.congr' ?_
        filter_upwards with m
        rw [Nat.add_comm]
      exact hcomp'.sub tendsto_const_nhds
    have hleft'' :
        Tendsto (fun m : ℕ => u (n + m) - u n) atTop
          (𝓝 (∑' i : ℕ, (u (i + n + 1) - u (i + n)))) := by
      refine hleft'.congr' ?_
      filter_upwards with m
      exact sum_range_succDiff u n m
    have hlim := tendsto_nhds_unique hleft'' hright
    rw [hlim]
    ring_nf

private lemma tendsto_zero_of_succDiff_isBigO_inv_cube
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_cube hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 3 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 3‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 3) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_cube :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) ≤
        2 / (n : ℝ) ^ 2 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_cube_shift (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 3) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 3) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 2 = 2 / (n : ℝ) ^ 2 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3)) ≤
        C * (2 / (n : ℝ) ^ 2) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_cube hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 2 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 2‖ = ((n : ℝ)⁻¹) ^ 2 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ = C * (2 / (n : ℝ) ^ 2) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 3) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 2) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 2‖ := hpow_rw.symm

private lemma tendsto_zero_of_succDiff_isBigO_inv_four
    {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0))
    (hdiff :
      (fun n : ℕ => u (n + 1) - u n)
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)) :
    u =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  rcases hdiff.exists_pos with ⟨C, hCpos, hC⟩
  have hd_summ : Summable d := summable_of_isBigO_inv_four hdiff
  refine IsBigO.of_bound (2 * C) ?_
  have hCbound := hC.bound
  rw [eventually_atTop] at hCbound
  rcases hCbound with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max N 2, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have htail_eq := eq_neg_tsum_succDiff hu hd_summ n
  have htail_summ : Summable (fun i : ℕ => d (i + n)) :=
    (summable_nat_add_iff n).mpr hd_summ
  have htail_norm_summ : Summable (fun i : ℕ => ‖d (i + n)‖) := by
    rw [summable_norm_iff]
    exact htail_summ
  have hnorm_le := norm_tsum_le_tsum_norm htail_norm_summ
  have hterm_le : ∀ i : ℕ,
      ‖d (i + n)‖ ≤ C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
    intro i
    have hikN : N ≤ i + n := le_trans hnN (by omega)
    have hb := hN (i + n) hikN
    have hnonneg : 0 ≤ (((i + n : ℕ) : ℝ)⁻¹) ^ 4 := by positivity
    have hnorm : ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 4‖ =
        (((i + n : ℕ) : ℝ)⁻¹) ^ 4 := by
      rw [Real.norm_of_nonneg hnonneg]
    calc
      ‖d (i + n)‖ ≤ C * ‖(((i + n : ℕ) : ℝ)⁻¹) ^ 4‖ := hb
      _ = C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
          rw [hnorm, one_div, inv_pow]
  have hmajor_summ : Summable (fun i : ℕ => C * (1 / (((i + n : ℕ)) : ℝ) ^ 4)) := by
    have hbase : Summable (fun i : ℕ => 1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
      have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 4) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
      exact (summable_nat_add_iff n).mpr h
    exact hbase.mul_left C
  have htsum_le :
      (∑' i : ℕ, ‖d (i + n)‖) ≤
        ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
    exact htail_norm_summ.tsum_le_tsum hterm_le hmajor_summ
  have htail_four :
      (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 4) ≤
        2 / (n : ℝ) ^ 3 := by
    have hn_pred : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_of_gt hnpos_nat)
    have h := tail_inv_four_shift (n - 1)
    have hleft :
        (∑' i : ℕ, 1 / (((i + (n - 1) + 1 : ℕ)) : ℝ) ^ 4) =
          (∑' i : ℕ, 1 / (((i + n : ℕ)) : ℝ) ^ 4) := by
      apply tsum_congr
      intro i
      rw [show i + (n - 1) + 1 = i + n from by omega]
    have hright : 2 / (((n - 1 : ℕ) : ℝ) + 1) ^ 3 = 2 / (n : ℝ) ^ 3 := by
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hn_pred
      rw [hcast]
    rwa [hleft, hright] at h
  have htail_bound :
      (∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4)) ≤
        C * (2 / (n : ℝ) ^ 3) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left htail_four hCpos.le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  have hpow_rw : 2 * C * ‖((n : ℝ)⁻¹) ^ 3‖ = C * (2 / (n : ℝ) ^ 3) := by
    rw [htarget_norm]
    field_simp [hnpos.ne']
  calc
    ‖u n‖ = ‖∑' i : ℕ, d (i + n)‖ := by
      rw [htail_eq, norm_neg]
    _ ≤ ∑' i : ℕ, ‖d (i + n)‖ := hnorm_le
    _ ≤ ∑' i : ℕ, C * (1 / (((i + n : ℕ)) : ℝ) ^ 4) := htsum_le
    _ ≤ C * (2 / (n : ℝ) ^ 3) := htail_bound
    _ = 2 * C * ‖((n : ℝ)⁻¹) ^ 3‖ := hpow_rw.symm

private lemma inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2 =
        -(1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| =
        1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 3) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 3 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 3‖ = ((n : ℝ)⁻¹) ^ 3 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 3‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma inv_sub_inv_succ_sub_inv_sq_add_inv_cube_isBigO_inv_four (a : ℝ) :
    (fun n : ℕ =>
      a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
        ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  refine IsBigO.of_bound ‖a‖ ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      (n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
          ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3 =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
  have hden_pos : 0 < (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by positivity
  have habs :
      |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
          ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3| =
        1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) := by
    rw [hdiff, abs_of_nonneg]
    positivity
  have hden_le : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 3 * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) ^ 2), hnpos.le]
  have htail_le :
      1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 4 := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 4) hden_le
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
        ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3)‖
        = ‖a‖ *
          |(n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
            ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * (1 / ((n : ℝ) ^ 3 * ((n : ℝ) + 1))) := by rw [habs]
    _ ≤ ‖a‖ * (1 / (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = ‖a‖ * ‖((n : ℝ)⁻¹) ^ 4‖ := by
          rw [htarget_norm, one_div, inv_pow]

private lemma inv_sq_sub_inv_succ_sq_sub_two_inv_cube_isBigO_inv_four (a : ℝ) :
    (fun n : ℕ =>
      a * (((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
        2 * ((n : ℝ)⁻¹) ^ 3))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  refine IsBigO.of_bound (5 * ‖a‖) ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hdiff :
      ((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
          2 * ((n : ℝ)⁻¹) ^ 3 =
        -((3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2)) := by
    field_simp [hnpos.ne', hn1pos.ne']
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
  have hden_pos : 0 < (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 := by positivity
  have hnum_nonneg : 0 ≤ 3 * (n : ℝ) + 2 := by positivity
  have habs :
      |((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
          2 * ((n : ℝ)⁻¹) ^ 3| =
        (3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) := by
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have htail_le :
      (3 * (n : ℝ) + 2) / ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) ≤
        5 / (n : ℝ) ^ 4 := by
    rw [div_le_div_iff₀ hden_pos (by positivity : 0 < (n : ℝ) ^ 4)]
    have hbasic :
        (3 * (n : ℝ) + 2) * (n : ℝ) ≤ 5 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    calc
      (3 * (n : ℝ) + 2) * (n : ℝ) ^ 4
          = ((3 * (n : ℝ) + 2) * (n : ℝ)) * (n : ℝ) ^ 3 := by ring
      _ ≤ (5 * ((n : ℝ) + 1) ^ 2) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hbasic (by positivity)
      _ = 5 * ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2) := by ring
  have htarget_nonneg : 0 ≤ ((n : ℝ)⁻¹) ^ 4 := by positivity
  have htarget_norm : ‖((n : ℝ)⁻¹) ^ 4‖ = ((n : ℝ)⁻¹) ^ 4 := by
    rw [Real.norm_of_nonneg htarget_nonneg]
  calc
    ‖a * (((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
        2 * ((n : ℝ)⁻¹) ^ 3)‖
        = ‖a‖ *
          |((n : ℝ)⁻¹) ^ 2 - ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
            2 * ((n : ℝ)⁻¹) ^ 3| := by
          rw [norm_mul]
          simp [Real.norm_eq_abs]
    _ = ‖a‖ * ((3 * (n : ℝ) + 2) /
          ((n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2)) := by rw [habs]
    _ ≤ ‖a‖ * (5 / (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left htail_le (norm_nonneg a)
    _ = 5 * ‖a‖ * ‖((n : ℝ)⁻¹) ^ 4‖ := by
          rw [htarget_norm]
          field_simp [hnpos.ne']

private lemma gammaSecondError_succDiff_isBigO_inv_cube
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  set_option backward.isDefEq.respectTransparency false in
    have hY1 := gammaRatioNorm_sub_one_isBigO_inv hα
    have hStep2 := gammaStep_sub_one_isBigO_inv_sq α
    have hStep3 := gammaStep_sub_isBigO_inv_cube α
    have hprod0 := hY1.mul hStep2
    have hprod :
        (fun n : ℕ => (gammaRatioNorm α n - 1) * (gammaStep α n - 1))
          =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
      refine hprod0.congr_right ?_
      intro n
      ring_nf
    have htail := inv_sub_inv_succ_sub_inv_sq_isBigO_inv_cube (c1 α)
    have hsum := (hStep3.add hprod).add htail
    have heq :
        (fun n : ℕ => gammaSecondError α (n + 1) - gammaSecondError α n) =ᶠ[atTop]
          (fun n : ℕ =>
            (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
              (gammaRatioNorm α n - 1) * (gammaStep α n - 1) +
              c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) - ((n : ℝ)⁻¹) ^ 2)) := by
      filter_upwards [gammaRatioNorm_succ hα] with n hrec
      unfold gammaSecondError
      rw [hrec]
      ring_nf
    exact heq.trans_isBigO hsum

private lemma gammaSecondError_tendsto_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaSecondError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_sub_one_isBigO_inv hα
  have hYlim : Tendsto (fun n : ℕ => gammaRatioNorm α n - 1) atTop (𝓝 0) :=
    hY.trans_tendsto (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcorr :
      Tendsto (fun n : ℕ => c1 α * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c1 α)
  simpa [gammaSecondError] using hYlim.sub hcorr

private theorem gammaRatioNorm_second_order
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - (1 + c1 α * (n : ℝ)⁻¹))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  have hdiff := gammaSecondError_succDiff_isBigO_inv_cube hα
  have hlim := gammaSecondError_tendsto_zero hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_cube hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaSecondError
    ring_nf

private lemma gammaRatioNorm_second_order_sub_form
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) := by
  exact (gammaRatioNorm_second_order hα).congr_left fun n => by ring_nf

private lemma const_mul_inv_isBigO_inv (a : ℝ) :
    (fun n : ℕ => a * (n : ℝ)⁻¹)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  exact (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).const_mul_left a

private lemma gammaThirdError_succDiff_isBigO_inv_four
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaThirdError α (n + 1) - gammaThirdError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
  have hStep4 := gammaStep_sub_third_isBigO_inv_four α
  have hStep2 := gammaStep_sub_one_isBigO_inv_sq α
  have hStep3 := gammaStep_sub_isBigO_inv_cube α
  have hY2 := gammaRatioNorm_second_order_sub_form hα
  have hprodY0 := hY2.mul hStep2
  have hprodY :
      (fun n : ℕ =>
        (gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹) *
          (gammaStep α n - 1))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
    refine hprodY0.congr_right ?_
    intro n
    ring_nf
  have hcx := const_mul_inv_isBigO_inv (c1 α)
  have hprodC0 := hcx.mul hStep3
  have hprodC :
      (fun n : ℕ =>
        c1 α * (n : ℝ)⁻¹ *
          (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2))
        =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) := by
    refine hprodC0.congr_right ?_
    intro n
    ring_nf
  have htail1 := inv_sub_inv_succ_sub_inv_sq_add_inv_cube_isBigO_inv_four (c1 α)
  have htail2 := inv_sq_sub_inv_succ_sq_sub_two_inv_cube_isBigO_inv_four (c2 α)
  have hsum := (((hStep4.add hprodY).add hprodC).add htail1).add htail2
  have heq :
      (fun n : ℕ => gammaThirdError α (n + 1) - gammaThirdError α n) =ᶠ[atTop]
        (fun n : ℕ =>
          (gammaStep α n -
            (1 - c1 α * ((n : ℝ)⁻¹) ^ 2 +
              d3 α * ((n : ℝ)⁻¹) ^ 3)) +
            (gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹) *
              (gammaStep α n - 1) +
            c1 α * (n : ℝ)⁻¹ *
              (gammaStep α n - 1 + c1 α * ((n : ℝ)⁻¹) ^ 2) +
            c1 α * ((n : ℝ)⁻¹ - (((n + 1 : ℕ) : ℝ)⁻¹) -
              ((n : ℝ)⁻¹) ^ 2 + ((n : ℝ)⁻¹) ^ 3) +
            c2 α * (((n : ℝ)⁻¹) ^ 2 -
              ((((n + 1 : ℕ) : ℝ)⁻¹) ^ 2) -
              2 * ((n : ℝ)⁻¹) ^ 3)) := by
    filter_upwards [gammaRatioNorm_succ hα] with n hrec
    unfold gammaThirdError
    rw [hrec]
    dsimp [c1, c2, d3]
    ring_nf
  exact heq.trans_isBigO hsum

private lemma gammaThirdError_tendsto_zero
    {α : ℝ} (hα : 0 < α) :
    Tendsto (gammaThirdError α) atTop (𝓝 0) := by
  have hY := gammaRatioNorm_second_order_sub_form hα
  have htarget :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hYlim :
      Tendsto (fun n : ℕ => gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹)
        atTop (𝓝 0) :=
    hY.trans_tendsto htarget
  have hc2 :
      Tendsto (fun n : ℕ => c2 α * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using htarget.const_mul (c2 α)
  change Tendsto
    (fun n : ℕ =>
      gammaRatioNorm α n - 1 - c1 α * (n : ℝ)⁻¹ -
        c2 α * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0)
  simpa only [sub_zero] using hYlim.sub hc2

private theorem gammaRatioNorm_third_order
    {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      gammaRatioNorm α n -
        (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hdiff := gammaThirdError_succDiff_isBigO_inv_four hα
  have hlim := gammaThirdError_tendsto_zero hα
  have h := tendsto_zero_of_succDiff_isBigO_inv_four hlim hdiff
  exact h.congr_left fun n => by
    unfold gammaThirdError
    ring_nf

theorem gamma_ratio_third_order {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ =>
      Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ (α - 1) *
          (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
            (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
              ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
  have hnorm := gammaRatioNorm_third_order hα
  have hnorm_rpow :
      (fun n : ℕ =>
        gammaRatioNorm α n -
          (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
    exact hnorm.congr_right fun n => (rpow_neg_three_eq_inv_cube_nat n).symm
  have hp : (fun n : ℕ => (n : ℝ) ^ (α - 1))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 1)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (n : ℝ) ^ (α - 1) *
          (gammaRatioNorm α n -
            (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2)))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (α - 4)) := by
    exact IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := α - 1) (b := -(3 : ℝ)) (c := α - 4) hp hnorm_rpow (by linarith)
  have heq :
      (fun n : ℕ =>
        Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ (α - 1) *
            (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
              (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
                ((n : ℝ)⁻¹) ^ 2)) =ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) ^ (α - 1) *
            (gammaRatioNorm α n -
              (1 + c1 α * (n : ℝ)⁻¹ + c2 α * ((n : ℝ)⁻¹) ^ 2))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos_nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 := (Real.rpow_pos_of_pos hnpos _).ne'
    unfold gammaRatioNorm c1 c2
    field_simp [hpow_ne]
  exact heq.trans_isBigO hmul

end
end

section
/-!
# Ternary trees and the Fuss-Catalan asymptotic

The number of full ternary trees with `n` internal nodes is
`1 / (2n + 1) * binom(3n,n)`.  This file proves the corresponding
Fuss-Catalan asymptotic directly from Stirling's formula.
-/

open Filter Asymptotics
open scoped Topology

lemma ternary_choose_dvd (n : ℕ) :
    2 * n + 1 ∣ Nat.choose (3 * n) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hrel := Nat.choose_succ_right_eq (3 * n) (n - 1)
    have hpred : n - 1 + 1 = n := Nat.sub_one_add_one hn
    have hsub : 3 * n - (n - 1) = 2 * n + 1 := by omega
    rw [hpred, hsub] at hrel
    have hdvd : 2 * n + 1 ∣ Nat.choose (3 * n) n * n := by
      rw [hrel, mul_comm]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime (2 * n + 1) n := by
      have h : 2 * n + 1 = (n + 1) + n := by omega
      rw [h, Nat.coprime_add_self_left]
      have h2 : n + 1 = 1 + n := by omega
      rw [h2, Nat.coprime_add_self_left]
      simp
    exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdvd)

lemma ternaryTreeCount_cast (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      ((Nat.choose (3 * n) n : ℕ) : ℝ) / (((2 * n + 1 : ℕ) : ℝ)) := by
  unfold ternaryTreeCount
  exact Nat.cast_div (ternary_choose_dvd n) (by positivity)

lemma choose_three_mul_cast (n : ℕ) :
    ((Nat.choose (3 * n) n : ℕ) : ℝ) =
      (((3 * n).factorial : ℕ) : ℝ) /
        ((((n.factorial : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ))) := by
  have hle : n ≤ 3 * n := by omega
  rw [Nat.cast_choose ℝ hle]
  have hsub : 3 * n - n = 2 * n := by omega
  rw [hsub]
end

section
/-!
# Second-order ternary-tree asymptotics

This file records the second-order constants for the Fuss-Catalan `p = 3`
ternary-tree numbers.  The correction is computed from the three positive
Gamma ratios obtained from the exact Fuss-Catalan closed form.
-/

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable section

def ternaryGammaRatio (α : ℝ) (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) + α) / Real.Gamma ((n : ℝ) + 1)

def ternaryGammaPrefactor (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (3 * n) * (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) *
    Real.sqrt Real.pi / (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ))

def gammaRatioSecondCoeff (α : ℝ) : ℝ :=
  α * (α - 1) / 2

def gammaRatioNormalizedError (α : ℝ) (n : ℕ) : ℝ :=
  ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) -
    (1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹)

def gammaRatioNormalizedFactor (α : ℝ) (n : ℕ) : ℝ :=
  1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹ + gammaRatioNormalizedError α n

def ternaryGammaNormalizedProduct (n : ℕ) : ℝ :=
  gammaRatioNormalizedFactor (1 / 3 : ℝ) n *
    gammaRatioNormalizedFactor (2 / 3 : ℝ) n /
    gammaRatioNormalizedFactor (3 / 2 : ℝ) n

lemma gammaRatioNormalizedFactor_eq (α : ℝ) (n : ℕ) :
    gammaRatioNormalizedFactor α n =
      ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) := by
  unfold gammaRatioNormalizedFactor gammaRatioNormalizedError
  ring

lemma ternary_gamma_ratio_correction :
    gammaRatioSecondCoeff (1 / 3 : ℝ) +
      gammaRatioSecondCoeff (2 / 3 : ℝ) -
      gammaRatioSecondCoeff (3 / 2 : ℝ) =
    ternaryRelativeSecondConstant := by
  unfold gammaRatioSecondCoeff ternaryRelativeSecondConstant
  norm_num

lemma gamma_one_third_mul_two_thirds :
    Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) =
      2 * Real.pi / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  rw [h, show Real.pi * (1 / 3 : ℝ) = Real.pi / 3 by ring,
    Real.sin_pi_div_three]
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)]

private lemma gamma_three_step (x : ℝ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0)
    (hx2 : x + 2 ≠ 0) :
    Real.Gamma (x + 3) = (x + 2) * (x + 1) * x * Real.Gamma x := by
  calc
    Real.Gamma (x + 3) = Real.Gamma ((x + 2) + 1) := by ring_nf
    _ = (x + 2) * Real.Gamma (x + 2) := Real.Gamma_add_one hx2
    _ = (x + 2) * ((x + 1) * Real.Gamma (x + 1)) := by
      rw [show x + 2 = (x + 1) + 1 by ring, Real.Gamma_add_one hx1]
    _ = (x + 2) * ((x + 1) * (x * Real.Gamma x)) := by
      rw [show x + 1 = x + 1 by rfl, Real.Gamma_add_one hx]
    _ = (x + 2) * (x + 1) * x * Real.Gamma x := by ring

lemma gamma_three_mul_nat_add_one (n : ℕ) :
    Real.Gamma ((3 * n : ℕ) + 1 : ℝ) =
      (3 : ℝ) ^ (3 * n) *
        Real.Gamma ((n : ℝ) + 1 / 3) *
        Real.Gamma ((n : ℝ) + 2 / 3) *
        Real.Gamma ((n : ℝ) + 1) /
        (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ)) := by
  induction n with
  | zero =>
      have hΓ13 : Real.Gamma (1 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
      have hΓ23 : Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
      field_simp [Real.Gamma_one, hΓ13, hΓ23]
      norm_num
  | succ n ih =>
      have hΓ13 : Real.Gamma (1 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
      have hΓ23 : Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
      have hbase_ne : Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
        mul_ne_zero hΓ13 hΓ23
      have hx : ((3 * n : ℕ) + 1 : ℝ) ≠ 0 := by positivity
      have hx1 : ((3 * n : ℕ) + 1 : ℝ) + 1 ≠ 0 := by positivity
      have hx2 : ((3 * n : ℕ) + 1 : ℝ) + 2 ≠ 0 := by positivity
      have hstep := gamma_three_step (((3 * n : ℕ) + 1 : ℝ)) hx hx1 hx2
      have hsucc13 :
          Real.Gamma ((n + 1 : ℕ) + 1 / 3 : ℝ) =
            ((n : ℝ) + 1 / 3) * Real.Gamma ((n : ℝ) + 1 / 3) := by
        have hne : (n : ℝ) + 1 / 3 ≠ 0 := by positivity
        calc
          Real.Gamma ((n + 1 : ℕ) + 1 / 3 : ℝ) =
              Real.Gamma (((n : ℝ) + 1 / 3) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
                ring
          _ = ((n : ℝ) + 1 / 3) * Real.Gamma ((n : ℝ) + 1 / 3) :=
              Real.Gamma_add_one hne
      have hsucc23 :
          Real.Gamma ((n + 1 : ℕ) + 2 / 3 : ℝ) =
            ((n : ℝ) + 2 / 3) * Real.Gamma ((n : ℝ) + 2 / 3) := by
        have hne : (n : ℝ) + 2 / 3 ≠ 0 := by positivity
        calc
          Real.Gamma ((n + 1 : ℕ) + 2 / 3 : ℝ) =
              Real.Gamma (((n : ℝ) + 2 / 3) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
                ring
          _ = ((n : ℝ) + 2 / 3) * Real.Gamma ((n : ℝ) + 2 / 3) :=
              Real.Gamma_add_one hne
      have hsucc1 :
          Real.Gamma ((n + 1 : ℕ) + 1 : ℝ) =
            ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) := by
        have hne : (n : ℝ) + 1 ≠ 0 := by positivity
        calc
          Real.Gamma ((n + 1 : ℕ) + 1 : ℝ) =
              Real.Gamma (((n : ℝ) + 1) + 1) := by
                congr 1
                norm_num [Nat.cast_add]
          _ = ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1) :=
              Real.Gamma_add_one hne
      calc
        Real.Gamma ((3 * (n + 1) : ℕ) + 1 : ℝ)
            = Real.Gamma (((3 * n : ℕ) + 1 : ℝ) + 3) := by
                congr 1
                norm_num [Nat.cast_add, Nat.cast_mul]
                ring
        _ = (((3 * n : ℕ) + 1 : ℝ) + 2) *
              (((3 * n : ℕ) + 1 : ℝ) + 1) *
              ((3 * n : ℕ) + 1 : ℝ) *
              Real.Gamma ((3 * n : ℕ) + 1 : ℝ) := hstep
        _ =
            (3 : ℝ) ^ (3 * (n + 1)) *
              Real.Gamma ((n + 1 : ℕ) + 1 / 3 : ℝ) *
              Real.Gamma ((n + 1 : ℕ) + 2 / 3 : ℝ) *
              Real.Gamma ((n + 1 : ℕ) + 1 : ℝ) /
              (Real.Gamma (1 / 3 : ℝ) * Real.Gamma (2 / 3 : ℝ)) := by
                rw [ih, hsucc13, hsucc23, hsucc1]
                field_simp [hbase_ne]
                norm_num [Nat.cast_add, Nat.cast_mul, pow_succ]
                ring

lemma gamma_two_mul_nat_add_two (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 3 / 2) =
      Real.Gamma ((2 * n : ℕ) + 2 : ℝ) *
        (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) * Real.sqrt Real.pi := by
  have h := Real.Gamma_mul_Gamma_add_half ((n : ℝ) + 1)
  have hhalf : (n : ℝ) + 1 + 1 / 2 = (n : ℝ) + 3 / 2 := by ring
  have harg : 2 * ((n : ℝ) + 1) = ((2 * n : ℕ) + 2 : ℝ) := by
    norm_num [Nat.cast_mul]
    ring
  have hexp : (1 : ℝ) - (((2 * n : ℕ) + 2 : ℝ)) = -(2 * (n : ℝ) + 1) := by
    norm_num [Nat.cast_mul]
    ring
  rwa [hhalf, harg, hexp] at h

lemma gamma_two_mul_nat_add_two_solved (n : ℕ) :
    Real.Gamma ((2 * n : ℕ) + 2 : ℝ) =
      (Real.Gamma ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 3 / 2)) /
        ((2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) * Real.sqrt Real.pi) := by
  have h := gamma_two_mul_nat_add_two n
  have hpow : (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hpow, hsqrt] at h ⊢
  linarith

lemma ternaryTreeCount_gamma_factorial (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      Real.Gamma ((3 * n : ℕ) + 1 : ℝ) /
        (Real.Gamma ((n : ℝ) + 1) *
          Real.Gamma ((2 * n : ℕ) + 2 : ℝ)) := by
  have hΓ3 : Real.Gamma ((3 * n : ℕ) + 1 : ℝ) = (((3 * n).factorial : ℕ) : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial (3 * n)
  have hΓn : Real.Gamma ((n : ℝ) + 1) = ((n.factorial : ℕ) : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial n
  have hΓ2 : Real.Gamma ((2 * n : ℕ) + 2 : ℝ) =
      (((2 * n + 1 : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ)) := by
    have h := Real.Gamma_nat_eq_factorial (2 * n + 1)
    have hfac : ((2 * n + 1).factorial : ℝ) =
        ((2 * n + 1 : ℕ) : ℝ) * (((2 * n).factorial : ℕ) : ℝ) := by
      rw [show 2 * n + 1 = (2 * n) + 1 by omega, Nat.factorial_succ]
      norm_num
    rw [← hfac]
    calc
      Real.Gamma ((2 * n : ℕ) + 2 : ℝ) =
          Real.Gamma ((2 * n + 1 : ℕ) + 1 : ℝ) := by
            congr 1
            norm_num [Nat.cast_add, Nat.cast_mul]
            ring
      _ = ((2 * n + 1).factorial : ℝ) := h
  rw [ternaryTreeCount_cast n, choose_three_mul_cast n, hΓ3, hΓn, hΓ2]
  have hnfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h2fac : (((2 * n).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hodd : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hnfac, h2fac, hodd]

lemma ternaryTreeCount_eq_gamma_ratios_raw (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      ternaryGammaPrefactor n *
        (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) := by
  rw [ternaryTreeCount_gamma_factorial n, gamma_three_mul_nat_add_one n,
    gamma_two_mul_nat_add_two_solved n]
  unfold ternaryGammaPrefactor ternaryGammaRatio
  have hΓ13 : Real.Gamma (1 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
  have hΓ23 : Real.Gamma (2 / 3 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
  have hΓn1 : Real.Gamma ((n : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
  have hΓn32 : Real.Gamma ((n : ℝ) + 3 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 3 / 2)).ne'
  have hpow : (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hΓ13, hΓ23, hΓn1, hΓn32, hpow, hsqrt]

lemma ternaryGammaPrefactor_eq (n : ℕ) :
    ternaryGammaPrefactor n =
      (27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant := by
  unfold ternaryGammaPrefactor ternaryAsymptoticConstant
  rw [gamma_one_third_mul_two_thirds]
  have h2rpow :
      (2 : ℝ) ^ (-(2 * (n : ℝ) + 1)) = ((2 : ℝ) ^ (2 * n + 1))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) by
      norm_num [Nat.cast_mul, Nat.cast_add]]
    rw [Real.rpow_natCast]
  rw [h2rpow]
  have hsqrtπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrtπ_sq : Real.sqrt Real.pi ^ 2 = Real.pi := by
    rw [Real.sq_sqrt Real.pi_nonneg]
  have h3pow : (3 : ℝ) ^ (3 * n) = 27 ^ n := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    rw [pow_mul]
  have h2pow : (2 : ℝ) ^ (2 * n + 1) = 2 * 4 ^ n := by
    rw [pow_add]
    norm_num
    rw [show (2 : ℝ) ^ (2 * n) = 4 ^ n by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      rw [pow_mul]]
    ring
  rw [h3pow, h2pow]
  field_simp [hsqrtπ, hsqrt3, hpi]
  rw [hsqrtπ_sq]
  rw [show (27 / 4 : ℝ) ^ n = 27 ^ n / 4 ^ n by rw [div_pow]]
  field_simp [pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0), hpi]
  ring

lemma ternaryTreeCount_eq_gamma_ratios (n : ℕ) :
    (ternaryTreeCount n : ℝ) =
      (27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant *
        (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) := by
  rw [ternaryTreeCount_eq_gamma_ratios_raw n, ternaryGammaPrefactor_eq n]

lemma ternaryGammaProduct_normalized_eq_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    (ternaryGammaRatio (1 / 3 : ℝ) n *
        ternaryGammaRatio (2 / 3 : ℝ) n /
        ternaryGammaRatio (3 / 2 : ℝ) n) /
      ((n : ℝ) ^ (-(3 / 2 : ℝ))) =
    ternaryGammaNormalizedProduct n := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hp1 : (n : ℝ) ^ ((1 / 3 : ℝ) - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hp2 : (n : ℝ) ^ ((2 / 3 : ℝ) - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hp3 : (n : ℝ) ^ ((3 / 2 : ℝ) - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hp : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hR3 : ternaryGammaRatio (3 / 2 : ℝ) n ≠ 0 := by
    unfold ternaryGammaRatio
    have hnum : Real.Gamma ((n : ℝ) + 3 / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 3 / 2)).ne'
    have hden : Real.Gamma ((n : ℝ) + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity : 0 < (n : ℝ) + 1)).ne'
    exact div_ne_zero hnum hden
  have hpow :
      (n : ℝ) ^ ((1 / 3 : ℝ) - 1) *
          (n : ℝ) ^ ((2 / 3 : ℝ) - 1) /
          (n : ℝ) ^ ((3 / 2 : ℝ) - 1) =
        (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    rw [← Real.rpow_neg hnpos.le]
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    norm_num
  unfold ternaryGammaNormalizedProduct
  rw [gammaRatioNormalizedFactor_eq, gammaRatioNormalizedFactor_eq,
    gammaRatioNormalizedFactor_eq]
  field_simp [hp1, hp2, hp3, hp, hR3]
  have hpow' :
      (n : ℝ) ^ (((1 : ℝ) - 3) / 3) *
          (n : ℝ) ^ (((2 : ℝ) - 3) / 3) =
        (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (n : ℝ) ^ (((3 : ℝ) - 2) / 2) := by
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
    congr 1
    norm_num
  calc
    ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          (n : ℝ) ^ (((1 : ℝ) - 3) / 3) *
          (n : ℝ) ^ (((2 : ℝ) - 3) / 3)
        =
        ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          ((n : ℝ) ^ (((1 : ℝ) - 3) / 3) *
            (n : ℝ) ^ (((2 : ℝ) - 3) / 3)) := by ring
    _ =
        ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          ((n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (n : ℝ) ^ (((3 : ℝ) - 2) / 2)) := by rw [hpow']
    _ =
        ternaryGammaRatio (1 / 3) n * ternaryGammaRatio (2 / 3) n *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (n : ℝ) ^ (((3 : ℝ) - 2) / 2) := by ring

end
end

/-!
# Third-order ternary-tree asymptotics

This file records the ternary-tree square-root data at `ρ = 4 / 27` and plugs
it into the committed third-order square-root applicator.  The unconditional
Gamma-ratio check at the end gives the same relative coefficient.
-/

set_option maxHeartbeats 1200000

open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries

noncomputable section

def ternaryTreeSeriesℂ : PowerSeries ℂ :=
  PowerSeries.mk fun n => (ternaryTreeCount n : ℂ)

@[simp] lemma coeff_ternaryTreeSeriesℂ (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n ternaryTreeSeriesℂ =
      (ternaryTreeCount n : ℂ) := by
  simp [ternaryTreeSeriesℂ]

def gammaRatioThirdCoeff (α : ℝ) : ℝ :=
  α * (α - 1) * (α - 2) * (3 * α - 1) / 24

def gammaRatioThirdNormalizedError (α : ℝ) (n : ℕ) : ℝ :=
  ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) -
    (1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹ +
      gammaRatioThirdCoeff α * ((n : ℝ)⁻¹) ^ 2)

def gammaRatioThirdNormalizedFactor (α : ℝ) (n : ℕ) : ℝ :=
  1 + gammaRatioSecondCoeff α * (n : ℝ)⁻¹ +
    gammaRatioThirdCoeff α * ((n : ℝ)⁻¹) ^ 2 +
      gammaRatioThirdNormalizedError α n

def ternaryGammaThirdNormalizedProduct (n : ℕ) : ℝ :=
  gammaRatioThirdNormalizedFactor (1 / 3 : ℝ) n *
    gammaRatioThirdNormalizedFactor (2 / 3 : ℝ) n /
    gammaRatioThirdNormalizedFactor (3 / 2 : ℝ) n

lemma gammaRatioThirdNormalizedFactor_eq (α : ℝ) (n : ℕ) :
    gammaRatioThirdNormalizedFactor α n =
      ternaryGammaRatio α n / ((n : ℝ) ^ (α - 1)) := by
  unfold gammaRatioThirdNormalizedFactor gammaRatioThirdNormalizedError
  ring

lemma ternaryGammaThirdNormalizedProduct_eq_second (n : ℕ) :
    ternaryGammaThirdNormalizedProduct n = ternaryGammaNormalizedProduct n := by
  unfold ternaryGammaThirdNormalizedProduct ternaryGammaNormalizedProduct
  rw [gammaRatioThirdNormalizedFactor_eq, gammaRatioThirdNormalizedFactor_eq,
    gammaRatioThirdNormalizedFactor_eq, gammaRatioNormalizedFactor_eq,
    gammaRatioNormalizedFactor_eq, gammaRatioNormalizedFactor_eq]

section
end

set_option backward.isDefEq.respectTransparency false in
lemma ternary_gamma_ratio_third_correction :
    gammaRatioThirdCoeff (1 / 3 : ℝ) +
      gammaRatioThirdCoeff (2 / 3 : ℝ) -
      gammaRatioThirdCoeff (3 / 2 : ℝ) +
      gammaRatioSecondCoeff (1 / 3 : ℝ) *
        gammaRatioSecondCoeff (2 / 3 : ℝ) +
      gammaRatioSecondCoeff (3 / 2 : ℝ) *
        gammaRatioSecondCoeff (3 / 2 : ℝ) -
      gammaRatioSecondCoeff (3 / 2 : ℝ) *
        gammaRatioSecondCoeff (1 / 3 : ℝ) -
      gammaRatioSecondCoeff (3 / 2 : ℝ) *
        gammaRatioSecondCoeff (2 / 3 : ℝ) =
    ternaryRelativeThirdConstant := by
  norm_num [gammaRatioSecondCoeff, gammaRatioThirdCoeff, ternaryRelativeThirdConstant]

lemma gammaRatioThirdNormalizedError_isBigO {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioThirdNormalizedError α n)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
  have hO := gamma_ratio_third_order (α := α) hα
  have hp : (fun n : ℕ => (n : ℝ) ^ (1 - α))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 - α)) := isBigO_refl _ _
  have hmul :
      (fun n : ℕ =>
        (ternaryGammaRatio α n -
          (n : ℝ) ^ (α - 1) *
            (1 + (α * (α - 1) / 2) * (n : ℝ)⁻¹ +
              (α * (α - 1) * (α - 2) * (3 * α - 1) / 24) *
                ((n : ℝ)⁻¹) ^ 2)) *
          (n : ℝ) ^ (1 - α))
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) := by
    simpa [ternaryGammaRatio] using
      IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (a := α - 4) (b := 1 - α) (c := -(3 : ℝ)) hO hp (by norm_num)
  refine hmul.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hpow_ne : (n : ℝ) ^ (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hpow_inv : (n : ℝ) ^ (1 - α) = ((n : ℝ) ^ (α - 1))⁻¹ := by
    rw [← Real.rpow_neg hnpos.le]
    congr 1
    ring
  unfold gammaRatioThirdNormalizedError gammaRatioSecondCoeff gammaRatioThirdCoeff
  rw [hpow_inv]
  field_simp [hpow_ne, hnne]

lemma gammaRatioThirdNormalizedError_isBigO_inv_cube {α : ℝ} (hα : 0 < α) :
    (fun n : ℕ => gammaRatioThirdNormalizedError α n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have h := gammaRatioThirdNormalizedError_isBigO (α := α) hα
  refine h.congr' (EventuallyEq.refl _ _) ?_
  filter_upwards with n
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num [inv_pow]

private lemma inv_nat_cube_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3

private lemma inv_nat_isBigO_one :
    (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ

private lemma inv_nat_sq_isBigO_one :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).isBigO_one ℝ

private lemma inv_nat_cube_isBigO_one :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) =O[atTop] (fun _n : ℕ => (1 : ℝ)) := by
  exact inv_nat_cube_tendsto_zero.isBigO_one ℝ

private lemma inv_nat_mul_inv_sq_isBigO_inv_cube :
    (fun n : ℕ => (n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine (isBigO_refl (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) atTop).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  ring

private lemma inv_nat_four_isBigO_inv_cube :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 4),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3)]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one (pow_nonneg hinv_nonneg 3)]

private lemma quadratic_error_mul_isBigO_inv_cube
    {e f : ℕ → ℝ} {a b c d : ℝ}
    (he : e =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3))
    (hf : f =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    (fun n : ℕ =>
      (1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2 + e n) *
          (1 + c * (n : ℝ)⁻¹ + d * ((n : ℝ)⁻¹) ^ 2 + f n) -
        (1 + (a + c) * (n : ℝ)⁻¹ + (b + d + a * c) * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have hI3 : (fun n : ℕ => (a * d + b * c) *
      ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_mul_inv_sq_isBigO_inv_cube.const_mul_left (a * d + b * c)
  have hI4 : (fun n : ℕ => b * d * ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_four_isBigO_inv_cube.const_mul_left (b * d)
  have hIf : (fun n : ℕ => a * (n : ℝ)⁻¹ * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_isBigO_one.const_mul_left a).mul hf
    simpa [Pi.mul_apply, mul_assoc] using h
  have hI2f : (fun n : ℕ => b * ((n : ℝ)⁻¹) ^ 2 * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_sq_isBigO_one.const_mul_left b).mul hf
    simpa [Pi.mul_apply, mul_assoc] using h
  have hIe : (fun n : ℕ => c * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_isBigO_one.const_mul_left c).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hI2e : (fun n : ℕ => d * ((n : ℝ)⁻¹) ^ 2 * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_sq_isBigO_one.const_mul_left d).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hf_one : f =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    hf.trans inv_nat_cube_isBigO_one
  have hef : (fun n : ℕ => e n * f n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := he.mul hf_one
    simpa [Pi.mul_apply] using h
  have hsum := (((((((hI3.add hI4).add hf).add he).add hIf).add hI2f).add hIe).add hI2e).add hef
  refine hsum.congr_left ?_
  intro n
  ring

section
end

set_option backward.isDefEq.respectTransparency false in
private lemma quadratic_error_inv_isBigO_inv_cube
    {e : ℕ → ℝ} {a b : ℝ}
    (he : e =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3)) :
    (fun n : ℕ =>
      (1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2 + e n)⁻¹ -
        (1 - a * (n : ℝ)⁻¹ + (a * a - b) * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  have he0 : Tendsto e atTop (𝓝 0) :=
    he.trans_tendsto inv_nat_cube_tendsto_zero
  have hlin0 : Tendsto (fun n : ℕ => a * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul a
  have hquad0 : Tendsto (fun n : ℕ => b * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul b
  have hden0 :
      Tendsto (fun n : ℕ => 1 + a * (n : ℝ)⁻¹ +
        b * ((n : ℝ)⁻¹) ^ 2 + e n) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds.add hlin0).add hquad0).add he0
  have hden_ne : ∀ᶠ n : ℕ in atTop,
      1 + a * (n : ℝ)⁻¹ + b * ((n : ℝ)⁻¹) ^ 2 + e n ≠ 0 :=
    hden0.eventually (compl_singleton_mem_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hden_inv_one :
      (fun n : ℕ => (1 + a * (n : ℝ)⁻¹ +
        b * ((n : ℝ)⁻¹) ^ 2 + e n)⁻¹)
        =O[atTop] (fun _n : ℕ => (1 : ℝ)) :=
    (hden0.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).isBigO_one ℝ
  have hI3 : (fun n : ℕ => -(a * a * a - 2 * a * b) *
      ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_mul_inv_sq_isBigO_inv_cube.const_mul_left (-(a * a * a - 2 * a * b))
  have hI4 : (fun n : ℕ => -(b * (a * a - b)) * ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) :=
    inv_nat_four_isBigO_inv_cube.const_mul_left (-(b * (a * a - b)))
  have hIe : (fun n : ℕ => a * (n : ℝ)⁻¹ * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_isBigO_one.const_mul_left a).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hI2e : (fun n : ℕ => -(a * a - b) * ((n : ℝ)⁻¹) ^ 2 * e n)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have h := (inv_nat_sq_isBigO_one.const_mul_left (-(a * a - b))).mul he
    simpa [Pi.mul_apply, mul_assoc] using h
  have hnum : (fun n : ℕ =>
      -e n + a * (n : ℝ)⁻¹ * e n -
        (a * a - b) * ((n : ℝ)⁻¹) ^ 2 * e n -
        (a * a * a - 2 * a * b) *
          ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2) -
        b * (a * a - b) * ((n : ℝ)⁻¹) ^ 4)
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    have hsum := (((he.neg_left.add hIe).add hI2e).add hI3).add hI4
    convert hsum using 1
    ext n
    ring_nf
  have hprod := hnum.mul hden_inv_one
  refine hprod.congr' ?_ ?_
  · filter_upwards [hden_ne] with n hne
    let I : ℝ := (n : ℝ)⁻¹
    let D : ℝ := 1 + a * I + b * I ^ 2 + e n
    let q : ℝ := 1 - a * I + (a * a - b) * I ^ 2
    let N : ℝ :=
      -e n + a * I * e n - (a * a - b) * I ^ 2 * e n -
        (a * a * a - 2 * a * b) * (I * I ^ 2) -
          b * (a * a - b) * I ^ 4
    change N * D⁻¹ = D⁻¹ - q
    have hD : D ≠ 0 := by
      simpa [D, I] using hne
    have hN : N = 1 - q * D := by
      dsimp [N, q, D]
      ring
    rw [hN]
    calc
      (1 - q * D) * D⁻¹ = D⁻¹ - q * (D * D⁻¹) := by ring
      _ = D⁻¹ - q * 1 := by rw [mul_inv_cancel₀ hD]
      _ = D⁻¹ - q := by ring
  · filter_upwards with n
    ring

theorem ternaryGammaThirdNormalizedProduct_thirdOrder :
    (fun n : ℕ =>
      ternaryGammaThirdNormalizedProduct n -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  let c₁ : ℝ := gammaRatioSecondCoeff (1 / 3 : ℝ)
  let c₂ : ℝ := gammaRatioSecondCoeff (2 / 3 : ℝ)
  let c₃ : ℝ := gammaRatioSecondCoeff (3 / 2 : ℝ)
  let d₁ : ℝ := gammaRatioThirdCoeff (1 / 3 : ℝ)
  let d₂ : ℝ := gammaRatioThirdCoeff (2 / 3 : ℝ)
  let d₃ : ℝ := gammaRatioThirdCoeff (3 / 2 : ℝ)
  let e₁ : ℕ → ℝ := gammaRatioThirdNormalizedError (1 / 3 : ℝ)
  let e₂ : ℕ → ℝ := gammaRatioThirdNormalizedError (2 / 3 : ℝ)
  let e₃ : ℕ → ℝ := gammaRatioThirdNormalizedError (3 / 2 : ℝ)
  let e₁₂ : ℕ → ℝ := fun n =>
    (1 + c₁ * (n : ℝ)⁻¹ + d₁ * ((n : ℝ)⁻¹) ^ 2 + e₁ n) *
        (1 + c₂ * (n : ℝ)⁻¹ + d₂ * ((n : ℝ)⁻¹) ^ 2 + e₂ n) -
      (1 + (c₁ + c₂) * (n : ℝ)⁻¹ +
        (d₁ + d₂ + c₁ * c₂) * ((n : ℝ)⁻¹) ^ 2)
  let e₃inv : ℕ → ℝ := fun n =>
    (1 + c₃ * (n : ℝ)⁻¹ + d₃ * ((n : ℝ)⁻¹) ^ 2 + e₃ n)⁻¹ -
      (1 - c₃ * (n : ℝ)⁻¹ + (c₃ * c₃ - d₃) * ((n : ℝ)⁻¹) ^ 2)
  have he₁ : e₁ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₁] using
      gammaRatioThirdNormalizedError_isBigO_inv_cube
        (α := (1 / 3 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 3)
  have he₂ : e₂ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₂] using
      gammaRatioThirdNormalizedError_isBigO_inv_cube
        (α := (2 / 3 : ℝ)) (by norm_num : (0 : ℝ) < 2 / 3)
  have he₃ : e₃ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₃] using
      gammaRatioThirdNormalizedError_isBigO_inv_cube
        (α := (3 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 3 / 2)
  have he₁₂ : e₁₂ =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₁₂] using
      quadratic_error_mul_isBigO_inv_cube
        (a := c₁) (b := d₁) (c := c₂) (d := d₂) he₁ he₂
  have he₃inv : e₃inv =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
    simpa [e₃inv] using
      quadratic_error_inv_isBigO_inv_cube (a := c₃) (b := d₃) he₃
  have hprod :=
    quadratic_error_mul_isBigO_inv_cube
      (e := e₁₂) (f := e₃inv)
      (a := c₁ + c₂) (b := d₁ + d₂ + c₁ * c₂)
      (c := -c₃) (d := c₃ * c₃ - d₃) he₁₂ he₃inv
  have hcorr₁ : c₁ + c₂ - c₃ = ternaryRelativeSecondConstant := by
    simpa [c₁, c₂, c₃] using ternary_gamma_ratio_correction
  have hcorr₂ :
      d₁ + d₂ - d₃ + c₁ * c₂ + c₃ * c₃ - c₃ * c₁ - c₃ * c₂ =
        ternaryRelativeThirdConstant := by
    simpa [c₁, c₂, c₃, d₁, d₂, d₃, mul_assoc, add_assoc, add_comm,
      add_left_comm, sub_eq_add_neg] using ternary_gamma_ratio_third_correction
  refine hprod.congr_left ?_
  intro n
  unfold ternaryGammaThirdNormalizedProduct gammaRatioThirdNormalizedFactor
  dsimp [e₁, e₂, e₃, e₁₂, e₃inv, c₁, c₂, c₃, d₁, d₂, d₃]
  rw [← hcorr₁, ← hcorr₂]
  ring

theorem ternaryGammaProduct_normalized_thirdOrder :
    (fun n : ℕ =>
      (ternaryGammaRatio (1 / 3 : ℝ) n *
          ternaryGammaRatio (2 / 3 : ℝ) n /
          ternaryGammaRatio (3 / 2 : ℝ) n) /
        ((n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine ternaryGammaThirdNormalizedProduct_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [ternaryGammaProduct_normalized_eq_of_one_le hn,
    ← ternaryGammaThirdNormalizedProduct_eq_second n]

end

set_option maxHeartbeats 1200000
open Complex Filter Asymptotics
open scoped Topology BigOperators PowerSeries
theorem solution :
    (fun n : ℕ =>
      (ternaryTreeCount n : ℝ) /
          ((27 / 4 : ℝ) ^ n * ternaryAsymptoticConstant *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) -
        (1 + ternaryRelativeSecondConstant * (n : ℝ)⁻¹ +
          ternaryRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =O[atTop] (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) := by
  refine ternaryGammaProduct_normalized_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hbase : (27 / 4 : ℝ) ^ n ≠ 0 :=
    pow_ne_zero n (by norm_num : (27 / 4 : ℝ) ≠ 0)
  have hK : ternaryAsymptoticConstant ≠ 0 := by
    unfold ternaryAsymptoticConstant
    positivity
  have hp : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  rw [ternaryTreeCount_eq_gamma_ratios n]
  field_simp [hbase, hK, hp]
