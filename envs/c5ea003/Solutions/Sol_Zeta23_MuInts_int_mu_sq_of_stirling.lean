-- Prove2me | solution 1 for Zeta23.MuInts.int_mu_sq_of_stirling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:56:54.971828+00:00
-- url     : https://prove2.me/submissions/098330b5-daad-4b5a-adfa-298d861235f4

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_IntMu
import Definitions.Def_Zeta23_GammaFacts_Series
import Theorems.Thm_Zeta23_MuInts_integral_main_sq_eq
import Theorems.Thm_Zeta23_mu_smooth

-- from Zeta23.GammaFacts.IntMu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/IntMu.lean — the [eq:muints] Γ-half integrals.
Paper: "∫_T^{2T} μ(τ)dτ = Tℓ₁/(2π) + O(1/T)", "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))",
via "(eq:muints) follows from (eq:mufacts) … and ∫_T^{2T} log²(τ/2π) dτ = T(ℓ₁² + 1 − 2log²2)".
Both theorems take the Stirling field as a hypothesis (hst); the Stirling asymptotic itself is
proved elsewhere in the repository, so GammaFacts assembles with no Γ-hypothesis beyond it.
-/

noncomputable section

namespace Zeta23
namespace MuInts

open MeasureTheory intervalIntegral






end MuInts
end Zeta23
end
open Zeta23
open MuInts
open MeasureTheory intervalIntegral
set_option maxHeartbeats 1600000

theorem solution (hst : StirlingHyp) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  obtain ⟨C, hC⟩ := hst
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hμcont : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  set C₂ : ℝ := C * (1 + C) + 1 with hC₂
  have hC₂0 : (0 : ℝ) < C₂ := by nlinarith
  refine ⟨8 * (1 + 2 * Real.log 2 ^ 2) + 1,
    max (2 * Real.pi * Real.exp 4) (32 * Real.pi ^ 2 * C₂), fun T hT => ?_⟩
  set m : ℝ := Real.log 2 with hm
  have hm0 : (0 : ℝ) < m := Real.log_pos (by norm_num)
  have hm1 : m < 1 := by
    rw [hm]
    have := Real.log_two_lt_d9
    linarith
  have hT1 : 2 * Real.pi * Real.exp 4 ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : 32 * Real.pi ^ 2 * C₂ ≤ T := le_trans (le_max_right _ _) hT
  have hexp1 : (1 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hT0 : (0 : ℝ) < T := by nlinarith [Real.exp_pos (4 : ℝ)]
  have hL4 : (4 : ℝ) ≤ l T := by
    unfold l
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    apply Real.log_le_log (Real.exp_pos 4)
    rw [le_div_iff₀ (by positivity)]
    linarith
  set L : ℝ := l T with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hL_le_T : L ≤ T := by
    rw [hLdef]
    unfold l
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / (2 * Real.pi))
    have h2 : T / (2 * Real.pi) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    linarith
  have hell : ell1 T = L + 2 * m - 1 := by
    unfold ell1
    rw [← hLdef, ← hm]
  have hell_pos : (0 : ℝ) < ell1 T := by
    rw [hell]
    nlinarith
  have hell_ge : L / 2 ≤ ell1 T := by
    rw [hell]
    nlinarith
  have hell2 : L ^ 2 / 4 ≤ ell1 T ^ 2 := by
    nlinarith [hell_ge, hL0, hell_pos]
  have hmain_bound : ∀ τ ∈ Set.Icc T (2 * T),
      |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ (L + m) / (2 * Real.pi) := by
    intro τ hτ
    have hτT : T ≤ τ := hτ.1
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτT
    have hlog_nonneg : (0 : ℝ) ≤ Real.log (τ / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hlog_le : Real.log (τ / (2 * Real.pi)) ≤ L + m := by
      have h1 : Real.log (τ / (2 * Real.pi)) ≤ Real.log (2 * T / (2 * Real.pi)) := by
        apply Real.log_le_log (by positivity)
        gcongr
        exact hτ.2
      have h2 : Real.log (2 * T / (2 * Real.pi)) = m + L := by
        rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
          Real.log_mul (by norm_num) (by positivity), hm, hLdef]
        rfl
      linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)),
      abs_of_nonneg hlog_nonneg]
    rw [one_div, div_eq_mul_inv (L + m), mul_comm (L + m)]
    exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
  have herr_bound : ∀ τ ∈ Set.Icc T (2 * T),
      |Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2|
        ≤ C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    intro τ hτ
    have hτT : T ≤ τ := hτ.1
    have hτ1 : (1 : ℝ) ≤ τ := by nlinarith
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have herr := hC τ (by rwa [habs])
    rw [habs] at herr
    have hmb := hmain_bound τ hτ
    have hsq : Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
        = (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
          * (Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
      ring
    rw [hsq, abs_mul]
    have hτ2 : (0 : ℝ) < τ ^ 2 := by positivity
    have hCτ : C / τ ^ 2 ≤ C := by
      rw [div_le_iff₀ hτ2]
      have hτsq1 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith
      nlinarith
    have hsum_bound : |Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
        ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by
      have h4 := abs_sub_abs_le_abs_sub (Zeta23.mu τ)
        ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      have h5 : |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C :=
        le_trans herr hCτ
      have h3 : |Zeta23.mu τ| ≤ (L + m) / (2 * Real.pi) + C := by linarith
      calc |Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
          ≤ |Zeta23.mu τ| + |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
            abs_add_le _ _
        _ ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by linarith
    exact mul_le_mul herr hsum_bound (abs_nonneg _) (by positivity)
  have hint_mu2 : IntervalIntegrable (fun τ : ℝ => Zeta23.mu τ ^ 2) volume T (2 * T) :=
    (hμcont.pow 2).intervalIntegrable _ _
  have hint_main2 : IntervalIntegrable
      (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
      volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.mul ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _))).pow 2).continuousWithinAt
  have hCtau2 : IntervalIntegrable
      (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.div (continuousAt_pow _ _) (by positivity)).mul
      continuousAt_const).continuousWithinAt
  have hmain2 : ∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
      = (1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2)) := by
    rw [show (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        = fun τ : ℝ => (1 / (4 * Real.pi ^ 2)) * Real.log (τ / (2 * Real.pi)) ^ 2
      from funext fun τ => by field_simp; ring]
    rw [intervalIntegral.integral_const_mul, integral_main_sq_eq hT0, hm]
  have hsplit : (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2)
      = (∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        + ∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2) := by
    rw [← intervalIntegral.integral_add hint_main2 (hint_mu2.sub hint_main2)]
    congr 1
    funext τ
    ring
  have hCint : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have hftc2 : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ :=
        (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      intro τ hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      exact (continuousAt_const.div (continuousAt_pow _ _)
        (by positivity)).continuousWithinAt
    rw [integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    field_simp
    ring
  have herrI : |∫ τ in T..(2 * T),
      (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
      ≤ (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    have hCint2 : ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)
        = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
      rw [show (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C))
          = fun τ : ℝ => (2 * ((L + m) / (2 * Real.pi)) + C) * (C / τ ^ 2)
        from funext fun τ => by ring]
      rw [intervalIntegral.integral_const_mul, hCint]
      ring
    calc |∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
        ≤ ∫ τ in T..(2 * T),
            |Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
      _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hint_mu2.sub hint_main2).abs hCtau2 ?_
          intro τ hτ
          exact herr_bound τ hτ
      _ = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := hCint2
  rw [hsplit, hmain2]
  set X : ℝ := T * ell1 T ^ 2 / (4 * Real.pi ^ 2) / L ^ 2 with hX
  have hX1 : T / (16 * Real.pi ^ 2) ≤ X := by
    rw [hX, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hell2, hT0.le, sq_nonneg L, mul_pos hT0 (mul_pos hπ hπ)]
  have hX0 : (0 : ℝ) < X := by
    rw [hX]
    positivity
  have htri : |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
          - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
    have h1 := abs_add_le
      ((1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2))
      (∫ τ in T..(2 * T),
        (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
    calc |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        + (∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        = |((1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
            - T * ell1 T ^ 2 / (4 * Real.pi ^ 2))
          + ∫ τ in T..(2 * T),
              (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
          congr 1
          ring
      _ ≤ _ := h1
  have hmain_dev : |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ 8 * (1 + 2 * m ^ 2) * X := by
    have h1 : (1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2) = T * (1 - 2 * m ^ 2) / (4 * Real.pi ^ 2) := by
      ring
    rw [h1, abs_div, abs_mul, abs_of_pos hT0,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)]
    have habs1 : |1 - 2 * m ^ 2| ≤ 1 + 2 * m ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg m]
    calc T * |1 - 2 * m ^ 2| / (4 * Real.pi ^ 2)
        ≤ T * (1 + 2 * m ^ 2) / (4 * Real.pi ^ 2) := by gcongr
      _ = 4 * (1 + 2 * m ^ 2) * (T / (16 * Real.pi ^ 2)) := by ring
      _ ≤ 4 * (1 + 2 * m ^ 2) * X := by
          gcongr
      _ ≤ 8 * (1 + 2 * m ^ 2) * X := by nlinarith [hX0, sq_nonneg m]
  have herr_final : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ 1 * X := by
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hb1 : 2 * ((L + m) / (2 * Real.pi)) ≤ L := by
      have h2a : (L + m) / (2 * Real.pi) ≤ (L + 1) / (2 * Real.pi) := by
        gcongr
      have h2b : (L + 1) / (2 * Real.pi) ≤ (L + 1) / 6 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
      have h3 : (L + 1) / 6 ≤ L / 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    have hb2 : 2 * ((L + m) / (2 * Real.pi)) + C ≤ (1 + C) * L := by
      have h4 : C ≤ C * L := by nlinarith
      nlinarith
    have hb3 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ C₂ * L / T := by
      have h5 : (0 : ℝ) ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by positivity
      have h6 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := by
        apply mul_le_mul_of_nonneg_left hb2 (by positivity)
      calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := h6
        _ = (C * (1 + C)) * L / (2 * T) := by ring
        _ ≤ C₂ * L / T := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            have h7 : (0 : ℝ) ≤ C * (1 + C) := by nlinarith
            nlinarith [mul_nonneg (mul_nonneg h7 hL0.le) hT0.le, hL0.le, hT0.le]
    have hb4 : C₂ * L / T ≤ C₂ := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have hb5 : C₂ ≤ T / (32 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hb6 : T / (32 * Real.pi ^ 2) ≤ T / (16 * Real.pi ^ 2) := by
      apply div_le_div_of_nonneg_left hT0.le (by positivity)
      nlinarith
    rw [one_mul]
    calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
        ≤ C₂ * L / T := hb3
      _ ≤ C₂ := hb4
      _ ≤ T / (32 * Real.pi ^ 2) := hb5
      _ ≤ T / (16 * Real.pi ^ 2) := hb6
      _ ≤ X := hX1
  calc |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
          - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := htri
    _ ≤ 8 * (1 + 2 * m ^ 2) * X + 1 * X := by
        have := le_trans herrI herr_final
        linarith [hmain_dev]
    _ = (8 * (1 + 2 * m ^ 2) + 1) * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / L ^ 2 := by
        rw [hX]
        ring
