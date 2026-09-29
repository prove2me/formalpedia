-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_Mform_cos_phase_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:34:00.129978+00:00
-- url     : https://prove2.me/submissions/3de0c4dc-8861-4a46-8d0c-36914320a9a1

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Theorems.Thm_Zeta23_PrimeSide_inner_ibp_phase
import Theorems.Thm_Zeta23_PrimeSide_outer_ibp

-- from Zeta23.PrimeSideA.CrossMuPCore
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Analytic core of [prop:cross] (i): the double integration by parts for `𝓜[u, cos(·y)]`

See `Zeta23/PrimeSideA/CrossMuP.lean` for the statement of [prop:cross](i) and the paper text.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

section CrossMuPCore
variable {Φ : ℝ → ℝ} {T : ℝ}

lemma Mform_integrableOn' (hΦ : Continuous Φ) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) :
    IntegrableOn (fun q : ℝ × ℝ => (Φ (q.1 - q.2)) ^ 2 * u q.1 * v q.2)
      ((Set.Icc T (2 * T)) ×ˢ (Set.Icc T (2 * T))) := by
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  apply Continuous.continuousOn
  fun_prop

/-- `∫_S Φ(x−y)² dy ≤ ∫_ℝ Φ²`. -/
lemma setIntegral_sq_shift_le_left (hΦint : Integrable (fun x => Φ x ^ 2)) (S : Set ℝ) (x : ℝ) :
    ∫ y in S, Φ (x - y) ^ 2 ≤ ∫ y, Φ y ^ 2 := by
  calc ∫ y in S, Φ (x - y) ^ 2 ≤ ∫ y, Φ (x - y) ^ 2 :=
        setIntegral_le_integral (hΦint.comp_sub_left x)
          (Filter.Eventually.of_forall fun y => sq_nonneg _)
    _ = ∫ y, Φ y ^ 2 := integral_sub_left_eq_self (fun y => Φ y ^ 2) volume x

/-- Icc-set-integral = interval integral (`T ≤ 2T`). -/
lemma setIntegral_Icc_eq_intervalIntegral (hT : 0 ≤ T) (f : ℝ → ℝ) :
    ∫ x in Icc T (2 * T), f x = ∫ x in T..(2 * T), f x := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

/-- Fubini for `𝓜` with the first variable outer:
`𝓜[u,v] = ∫_I u(τ) (∫_I Φ(τ−τ′)² v(τ′) dτ′) dτ`. -/
lemma Mform_eq_iter (hΦ : Continuous Φ) {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) :
    Mform Φ T u v
      = ∫ τ in Icc T (2 * T), u τ * ∫ τ' in Icc T (2 * T), Φ (τ - τ') ^ 2 * v τ' := by
  unfold Mform
  rw [Measure.volume_eq_prod, setIntegral_prod _ (Mform_integrableOn' hΦ hu hv)]
  refine setIntegral_congr_fun measurableSet_Icc fun τ _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun τ' => by ring)

/-- `∫_S Φ(y − c)² dy ≤ ∫_ℝ Φ²` (translation invariance, `Φ² ≥ 0`). -/
lemma setIntegral_sq_shift_le' (hΦint : Integrable (fun x => Φ x ^ 2)) (S : Set ℝ) (c : ℝ) :
    ∫ y in S, Φ (y - c) ^ 2 ≤ ∫ y, Φ y ^ 2 := by
  calc ∫ y in S, Φ (y - c) ^ 2 ≤ ∫ y, Φ (y - c) ^ 2 :=
        setIntegral_le_integral (hΦint.comp_sub_right c)
          (Filter.Eventually.of_forall fun y => sq_nonneg _)
    _ = ∫ y, Φ y ^ 2 := integral_sub_right_eq_self (fun y => Φ y ^ 2) c





end CrossMuPCore

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hT : 0 ≤ T) (hΦ : ContDiff ℝ 1 Φ)
    (hΦint : Integrable (fun x => Φ x ^ 2)) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {B D : ℝ}
    (hB : ∀ τ ∈ Set.Icc T (2 * T), |u τ| ≤ B) (hD : ∀ τ ∈ Set.Icc T (2 * T), |deriv u τ| ≤ D)
    {y : ℝ} (hy : y ≠ 0) (θ : ℝ) :
    |Mform Φ T u (fun t => Real.cos (t * y + θ))| ≤ (4 * B + D * T) * (∫ x, Φ x ^ 2) / |y| := by

  -- notation
  set S : ℝ := ∫ x, Φ x ^ 2 with hS
  set Ψ : ℝ → ℝ := fun x => Φ x ^ 2 with hΨdef
  set ψ : ℝ → ℝ := deriv Ψ with hψdef
  have hΨ : ContDiff ℝ 1 Ψ := hΦ.pow 2
  have hΦc : Continuous Φ := hΦ.continuous
  have hΨc : Continuous Ψ := hΨ.continuous
  have hψc : Continuous ψ := hΨ.continuous_deriv le_rfl
  have huc : Continuous u := hu.continuous
  have hu'c : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hIm : MeasurableSet (Icc T (2 * T)) := measurableSet_Icc
  have hTI : T ∈ Icc T (2 * T) := ⟨le_rfl, by linarith⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB T hTI)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD T hTI)
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  have hΨnn : ∀ x, 0 ≤ Ψ x := fun x => sq_nonneg _
  have hvol : volume.real (Icc T (2 * T)) = T := by
    rw [Real.volume_real_Icc, max_eq_left (by linarith)]; ring
  -- the pieces
  set A : ℝ → ℝ := fun τ => Ψ (τ - 2 * T) * Real.sin (2 * T * y + θ) - Ψ (τ - T) * Real.sin (T * y + θ)
    with hAdef
  set F : ℝ → ℝ → ℝ := fun τ τ' => u τ * ψ (τ - τ') * Real.sin (τ' * y + θ) with hFdef
  have hFc : Continuous (Function.uncurry F) := by
    show Continuous (fun q : ℝ × ℝ => u q.1 * ψ (q.1 - q.2) * Real.sin (q.2 * y + θ))
    fun_prop
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (Icc T (2 * T))).prod (volume.restrict (Icc T (2 * T)))) := by
    rw [Measure.prod_restrict]
    exact (hFc.continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- Step 1: Fubini + inner IBP:  M = y⁻¹ (∫_I u A + ∫_I ∫_I F)
  have step1 : Mform Φ T u (fun t => Real.cos (t * y + θ))
      = y⁻¹ * ((∫ τ in Icc T (2 * T), u τ * A τ) + ∫ τ in Icc T (2 * T), ∫ τ' in Icc T (2 * T), F τ τ') := by
    rw [Mform_eq_iter hΦc huc (by fun_prop)]
    have hinner : ∀ τ, ∫ τ' in Icc T (2 * T), Φ (τ - τ') ^ 2 * Real.cos (τ' * y + θ)
        = A τ / y + y⁻¹ * ∫ τ' in Icc T (2 * T), ψ (τ - τ') * Real.sin (τ' * y + θ) := by
      intro τ
      rw [setIntegral_Icc_eq_intervalIntegral hT, setIntegral_Icc_eq_intervalIntegral hT,
        inner_ibp_phase hΦ hy θ τ]
    simp_rw [hinner]
    have hint1 : IntegrableOn (fun τ => u τ * A τ) (Icc T (2 * T)) := by
      apply Continuous.integrableOn_Icc; simp only [hAdef]; fun_prop
    have hint2 : IntegrableOn (fun τ => ∫ τ' in Icc T (2 * T), F τ τ') (Icc T (2 * T)) := by
      have := hFint.integral_prod_left
      simpa [IntegrableOn, Function.uncurry_def] using this
    have e : ∀ τ, u τ * (A τ / y + y⁻¹ * ∫ τ' in Icc T (2 * T), ψ (τ - τ') * Real.sin (τ' * y + θ))
        = y⁻¹ * (u τ * A τ) + y⁻¹ * ∫ τ' in Icc T (2 * T), F τ τ' := by
      intro τ
      have hF' : ∫ τ' in Icc T (2 * T), F τ τ'
          = u τ * ∫ τ' in Icc T (2 * T), ψ (τ - τ') * Real.sin (τ' * y + θ) := by
        rw [← integral_const_mul]
        congr 1; ext τ'; simp only [hFdef]; ring
      rw [hF']; field_simp
    simp_rw [e]
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul]
    ring
  -- Step 2: swap + outer IBP:  ∫_I ∫_I F = ∫_I sin(τ'y) (u(2T)Ψ(2T-τ') - u(T)Ψ(T-τ') - ∫_I u'Ψ(τ-τ'))
  have step2 : ∫ τ in Icc T (2 * T), ∫ τ' in Icc T (2 * T), F τ τ'
      = ∫ τ' in Icc T (2 * T), Real.sin (τ' * y + θ) * (u (2 * T) * Ψ (2 * T - τ') - u T * Ψ (T - τ')
          - ∫ τ in Icc T (2 * T), deriv u τ * Ψ (τ - τ')) := by
    rw [integral_integral_swap hFint]
    refine setIntegral_congr_fun hIm fun τ' _ => ?_
    have : (fun τ => F τ τ') = fun τ => Real.sin (τ' * y + θ) * (u τ * ψ (τ - τ')) := by
      ext τ; simp only [hFdef]; ring
    rw [this, integral_const_mul]
    congr 1
    rw [setIntegral_Icc_eq_intervalIntegral hT, setIntegral_Icc_eq_intervalIntegral hT]
    exact outer_ibp hΦ hu τ'
  -- Step 3: bounds
  have bd1 : |∫ τ in Icc T (2 * T), u τ * A τ| ≤ 2 * B * S := by
    have hg : IntegrableOn (fun τ => B * (Ψ (τ - 2 * T) + Ψ (τ - T))) (Icc T (2 * T)) := by
      apply Continuous.integrableOn_Icc; fun_prop
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le hg ?_).trans ?_
    · refine ae_restrict_of_forall_mem hIm fun τ hτ => ?_
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hB τ hτ) ?_ (abs_nonneg _) hB0
      simp only [hAdef]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (hΨnn _), abs_of_nonneg (hΨnn _)]
      nlinarith [Real.abs_sin_le_one (2 * T * y + θ), Real.abs_sin_le_one (T * y + θ), hΨnn (τ - 2 * T),
        hΨnn (τ - T), abs_nonneg (Real.sin (2 * T * y + θ)), abs_nonneg (Real.sin (T * y + θ))]
    · have i1 : IntegrableOn (fun τ => Ψ (τ - 2 * T)) (Icc T (2 * T)) := by
        apply Continuous.integrableOn_Icc; fun_prop
      have i2 : IntegrableOn (fun τ => Ψ (τ - T)) (Icc T (2 * T)) := by
        apply Continuous.integrableOn_Icc; fun_prop
      rw [integral_const_mul, integral_add i1 i2]
      have h1 := setIntegral_sq_shift_le' hΦint (Icc T (2 * T)) (2 * T)
      have h2 := setIntegral_sq_shift_le' hΦint (Icc T (2 * T)) T
      simp only [hΨdef] at h1 h2 ⊢
      nlinarith
  have bd2 : |∫ τ' in Icc T (2 * T), Real.sin (τ' * y + θ) * (u (2 * T) * Ψ (2 * T - τ') - u T * Ψ (T - τ')
          - ∫ τ in Icc T (2 * T), deriv u τ * Ψ (τ - τ'))| ≤ 2 * B * S + D * S * T := by
    have h2T : (2 * T) ∈ Icc T (2 * T) := ⟨by linarith, le_rfl⟩
    have hg : IntegrableOn (fun τ' => B * Ψ (2 * T - τ') + B * Ψ (T - τ') + D * S) (Icc T (2 * T)) := by
      apply Continuous.integrableOn_Icc; fun_prop
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le hg ?_).trans ?_
    · refine ae_restrict_of_forall_mem hIm fun τ' hτ' => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hsin := Real.abs_sin_le_one (τ' * y + θ)
      have hin : |∫ τ in Icc T (2 * T), deriv u τ * Ψ (τ - τ')| ≤ D * S := by
        have hg' : IntegrableOn (fun τ => D * Ψ (τ - τ')) (Icc T (2 * T)) := by
          apply Continuous.integrableOn_Icc; fun_prop
        refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le hg' ?_).trans ?_
        · refine ae_restrict_of_forall_mem hIm fun τ hτ => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΨnn _)]
          exact mul_le_mul_of_nonneg_right (hD τ hτ) (hΨnn _)
        · rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (setIntegral_sq_shift_le' hΦint (Icc T (2 * T)) τ') hD0
      have hmain : |u (2 * T) * Ψ (2 * T - τ') - u T * Ψ (T - τ') - ∫ τ in Icc T (2 * T), deriv u τ * Ψ (τ - τ')|
          ≤ B * Ψ (2 * T - τ') + B * Ψ (T - τ') + D * S := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) hin)
        · rw [abs_mul, abs_of_nonneg (hΨnn _)]
          exact mul_le_mul_of_nonneg_right (hB _ h2T) (hΨnn _)
        · rw [abs_mul, abs_of_nonneg (hΨnn _)]
          exact mul_le_mul_of_nonneg_right (hB _ hTI) (hΨnn _)
      calc |Real.sin (τ' * y + θ)| * |u (2 * T) * Ψ (2 * T - τ') - u T * Ψ (T - τ')
              - ∫ τ in Icc T (2 * T), deriv u τ * Ψ (τ - τ')|
          ≤ 1 * (B * Ψ (2 * T - τ') + B * Ψ (T - τ') + D * S) :=
            mul_le_mul hsin hmain (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [integral_add, integral_add, integral_const_mul, integral_const_mul, setIntegral_const,
        hvol, smul_eq_mul]
      · have h1 := setIntegral_sq_shift_le_left hΦint (Icc T (2 * T)) (2 * T)
        have h2 := setIntegral_sq_shift_le_left hΦint (Icc T (2 * T)) T
        simp only [hΨdef] at h1 h2 ⊢
        nlinarith
      all_goals { apply Continuous.integrableOn_Icc; fun_prop }
  -- conclude
  rw [step1, step2, abs_mul, abs_inv]
  rw [div_eq_mul_inv, mul_comm ((4 * B + D * T) * S) |y|⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (abs_nonneg _))
  refine (abs_add_le _ _).trans ?_
  nlinarith [bd1, bd2]
