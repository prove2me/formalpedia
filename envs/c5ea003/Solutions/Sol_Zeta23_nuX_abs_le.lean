-- Prove2me | solution 1 for Zeta23.nuX_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:24:49.596399+00:00
-- url     : https://prove2.me/submissions/d430df74-315b-432e-82b4-271739701a0c

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Theorems.Thm_Zeta23_Cheb_chebyshevMertens
import Theorems.Thm_Zeta23_PX_abs_le
import Theorems.Thm_Zeta23_PiX_abs_le

-- from Zeta23.PiFacts
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PiFacts.lean — [eq:PiPfacts], first clause: the pointwise bound for the
pole density Π_X of [eq:Pidef],

    "|Π_X(τ)| ≤ 3√X/(1+|τ|)"        (the paper, [eq:PiPfacts])

proved here for all X ≥ 1 (the paper applies it with X = e^L → ∞, so any
threshold suffices; no threshold is needed), together with continuity of
Π_X(·) (consumed for integrability).  Consumer: Zeta23/PrimeSideA.lean
(LocalHyps.PiX_bound).

Key inequalities: (1+|τ|)² ≤ 5(1/4+τ²) (so 1/|s| ≤ √5/(1+|τ|) for s = ½+iτ),
|X^s − 1| ≤ √X + 1 ≤ 2√X, and 5/(2π) + 2√5/π < 3.
-/

namespace Zeta23

open Real




/-! ### [eq:Bdef]: the pointwise bound |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X

Paper (after [eq:deltan]): "We shall use the following pointwise bound for ν_X.
By (eq:mufacts), (eq:PiPfacts) and (eq:cheb1), for T ≥ T₀,
  |ν_X(τ)| ≤ B + log⁺(|τ|/4T)  (τ ∈ ℝ),  |ν_X(τ)| ≤ B  (|τ| ≤ 4T),
  B := l + 4√X,  B² ≪ l² + X."                                        [eq:Bdef]

The μ-part consumes the H-Γ fields, so these lemmas take
hΓ : GammaFacts as a hypothesis — conditional on H-Γ exactly as the paper's §5.
The P_X-part uses the Chebyshev bound Zeta23.Cheb.chebyshevMertens.cheb1b
(paper's literal Σ_{n≤X} Λ(n)/√n ≤ 3√X for X ≥ x₀, absorbed into T₀), so no
Chebyshev hypothesis is needed. -/

section NuBound






end NuBound

end Zeta23
open Zeta23
open Real
set_option maxHeartbeats 1000000

theorem solution (hΓ : GammaFacts) {lam : ℝ} (hlam0 : 0 < lam) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T, T₀ ≤ T → ∀ τ : ℝ,
      |nuX (Real.exp (lam * l T)) τ|
        ≤ (l T + 4 * Real.sqrt (Real.exp (lam * l T)))
          + max (Real.log (|τ| / (4 * T))) 0 := by
  obtain ⟨C₁, hC₁⟩ := hΓ.stirling
  obtain ⟨x₀, hx₀⟩ := Zeta23.Cheb.chebyshevMertens.cheb1b
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- C₁ ≥ 0 (evaluate the Stirling bound at τ = 1)
  have hC₁0 : 0 ≤ C₁ := by
    have h := hC₁ 1 (by norm_num)
    have := abs_nonneg (mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  -- choose T₀
  set c₁ : ℝ := (C₁ + 2) / (1 - 1 / (2 * Real.pi)) with hc₁
  set c₂ : ℝ := Real.log (max x₀ 1) / lam with hc₂
  refine ⟨max (max (2 * Real.pi * Real.exp c₁) (2 * Real.pi * Real.exp c₂))
    (max 1 (2 * Real.pi)), le_max_of_le_right (le_max_left _ _), fun T hT τ => ?_⟩
  -- unpack the conditions on T
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT2π : 2 * Real.pi ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog_mono : ∀ c : ℝ, 2 * Real.pi * Real.exp c ≤ T → c ≤ l T := by
    intro c hc
    unfold l
    rw [show c = Real.log (Real.exp c) from (Real.log_exp c).symm]
    apply Real.log_le_log (Real.exp_pos c)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlc₁ : c₁ ≤ l T :=
    hlog_mono c₁ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT)
  have hlc₂ : c₂ ≤ l T :=
    hlog_mono c₂ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)
  have hl0 : 0 ≤ l T := by
    unfold l
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  set X : ℝ := Real.exp (lam * l T) with hX
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hXx₀ : x₀ ≤ X := by
    calc x₀ ≤ max x₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max x₀ 1)) :=
          (Real.exp_log (by positivity : (0 : ℝ) < max x₀ 1)).symm
      _ ≤ X := by
          rw [hX]
          apply Real.exp_le_exp.mpr
          calc Real.log (max x₀ 1) = lam * c₂ := by
                rw [hc₂, mul_div_cancel₀ _ (ne_of_gt hlam0)]
            _ ≤ lam * l T := mul_le_mul_of_nonneg_left hlc₂ hlam0.le
  have hsX1 : (1 : ℝ) ≤ Real.sqrt X := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hX1
  have hsX0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
  clear_value X
  -- the three pieces
  -- (Π) |Π_X τ| ≤ 3√X
  have hPiB : |PiX X τ| ≤ 3 * Real.sqrt X := by
    calc |PiX X τ| ≤ 3 * Real.sqrt X / (1 + |τ|) := PiX_abs_le hX1 τ
      _ ≤ 3 * Real.sqrt X / 1 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
          simp [abs_nonneg]
      _ = 3 * Real.sqrt X := by ring
  -- (P) |P_X τ| ≤ (3/π)√X ≤ √X
  have hP : |PX X τ| ≤ Real.sqrt X := by
    calc |PX X τ| ≤ (1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n := PX_abs_le X τ
      _ ≤ (1 / Real.pi) * (3 * Real.sqrt X) := by
          apply mul_le_mul_of_nonneg_left (hx₀ X hXx₀) (by positivity)
      _ ≤ Real.sqrt X := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
          nlinarith
  -- (μ) upper bound
  have hμle : mu τ ≤ 1 / (2 * Real.pi) * l T + (C₁ + 1)
      + max (Real.log (|τ| / (4 * T))) 0 := by
    have hmax0 : (0 : ℝ) ≤ max (Real.log (|τ| / (4 * T))) 0 := le_max_right _ _
    rcases le_or_gt (|τ|) 1 with hτ1 | hτ1
    · -- |τ| ≤ 1 : μ(τ) = μ(|τ|) ≤ μ(1) ≤ C₁ + (1/2π)log(1/2π) ≤ C₁
      have hμeven : mu τ = mu (|τ|) := by
        rcases abs_cases τ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
        · rw [h, hΓ.even]
      have hmono := hΓ.monotoneOn (a := |τ|) (b := 1)
        (by simp [abs_nonneg]) (by norm_num) hτ1
      have hμ1 : mu 1 ≤ C₁ := by
        have h := hC₁ 1 (by norm_num)
        have habs := abs_le.mp h
        have hlogneg : Real.log (|(1 : ℝ)| / (2 * Real.pi)) ≤ 0 := by
          apply Real.log_nonpos (by positivity)
          rw [abs_one, div_le_one (by positivity)]
          linarith
        have h2π : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
        nlinarith [habs.2]
      rw [hμeven]
      have hthis : mu (|τ|) ≤ C₁ := le_trans hmono hμ1
      have h2πl : (0 : ℝ) ≤ 1 / (2 * Real.pi) * l T := by positivity
      linarith
    · -- |τ| ≥ 1 : Stirling
      have hτ0 : (0 : ℝ) < |τ| := by linarith
      have h := (abs_le.mp (hC₁ τ hτ1.le)).2
      have hτsq : C₁ / τ ^ 2 ≤ C₁ := by
        have hτsq1 : (1 : ℝ) ≤ τ ^ 2 := by
          have := sq_abs τ
          nlinarith
        rw [div_le_iff₀ (by nlinarith)]
        nlinarith
      have hstep : mu τ ≤ 1 / (2 * Real.pi) * Real.log (|τ| / (2 * Real.pi)) + C₁ := by
        nlinarith
      have hlogsplit : Real.log (|τ| / (2 * Real.pi))
          = Real.log (|τ| / (4 * T)) + Real.log (4 * T / (2 * Real.pi)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      have hlog4T : Real.log (4 * T / (2 * Real.pi)) ≤ l T + Real.log 4 := by
        unfold l
        rw [show 4 * T / (2 * Real.pi) = 4 * (T / (2 * Real.pi)) by ring,
          Real.log_mul (by norm_num) (by positivity)]
        linarith
      have hlogτ4T : Real.log (|τ| / (4 * T)) ≤ max (Real.log (|τ| / (4 * T))) 0 :=
        le_max_left _ _
      have h2π : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
      have h2π1 : 1 / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have hlog4 : Real.log 4 ≤ 2 := by
        have h4 : (4 : ℝ) ≤ Real.exp 2 := by
          have h1 := Real.exp_one_gt_d9
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
            rw [← Real.exp_add]
            norm_num
          nlinarith
        calc Real.log 4 ≤ Real.log (Real.exp 2) :=
              Real.log_le_log (by norm_num) h4
          _ = 2 := Real.log_exp 2
      calc mu τ ≤ 1 / (2 * Real.pi) * Real.log (|τ| / (2 * Real.pi)) + C₁ := hstep
        _ = 1 / (2 * Real.pi) * Real.log (|τ| / (4 * T))
            + 1 / (2 * Real.pi) * Real.log (4 * T / (2 * Real.pi)) + C₁ := by
            rw [hlogsplit]
            ring
        _ ≤ max (Real.log (|τ| / (4 * T))) 0
            + 1 / (2 * Real.pi) * (l T + Real.log 4) + C₁ := by
            have hb1 : 1 / (2 * Real.pi) * Real.log (|τ| / (4 * T))
                ≤ max (Real.log (|τ| / (4 * T))) 0 := by
              rcases le_or_gt (Real.log (|τ| / (4 * T))) 0 with hneg | hpos
              · calc 1 / (2 * Real.pi) * Real.log (|τ| / (4 * T)) ≤ 0 := by nlinarith
                  _ ≤ max _ 0 := le_max_right _ _
              · calc 1 / (2 * Real.pi) * Real.log (|τ| / (4 * T))
                    ≤ Real.log (|τ| / (4 * T)) := by nlinarith
                  _ ≤ max _ 0 := le_max_left _ _
            have hb2 : 1 / (2 * Real.pi) * Real.log (4 * T / (2 * Real.pi))
                ≤ 1 / (2 * Real.pi) * (l T + Real.log 4) :=
              mul_le_mul_of_nonneg_left hlog4T h2π.le
            linarith
        _ ≤ 1 / (2 * Real.pi) * l T + (C₁ + 1) + max (Real.log (|τ| / (4 * T))) 0 := by
            have h6 : 1 / (2 * Real.pi) ≤ 1 / 6 :=
              one_div_le_one_div_of_le (by norm_num) (by linarith)
            have hlog40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
            have hconst : 1 / (2 * Real.pi) * Real.log 4 ≤ 1 / 6 * 2 :=
              mul_le_mul h6 hlog4 hlog40 (by norm_num)
            linarith
  -- (μ) lower bound: μ ≥ μ(0) > −1
  have hμge : -1 ≤ mu τ := by
    have h1 := hΓ.mu_zero_le τ
    have h2 := hΓ.neg_one_lt_mu_zero
    linarith
  have hμabs : |mu τ| ≤ 1 / (2 * Real.pi) * l T + (C₁ + 2)
      + max (Real.log (|τ| / (4 * T))) 0 := by
    rw [abs_le]
    constructor
    · have hmax0 : (0 : ℝ) ≤ max (Real.log (|τ| / (4 * T))) 0 := le_max_right _ _
      have h2π : (0 : ℝ) ≤ 1 / (2 * Real.pi) * l T := by positivity
      linarith
    · linarith
  -- assemble
  have hslack : C₁ + 2 ≤ (1 - 1 / (2 * Real.pi)) * l T := by
    have hden : (0 : ℝ) < 1 - 1 / (2 * Real.pi) := by
      have : 1 / (2 * Real.pi) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      linarith
    calc C₁ + 2 = (1 - 1 / (2 * Real.pi)) * c₁ := by
          rw [hc₁, mul_div_cancel₀ _ (ne_of_gt hden)]
      _ ≤ (1 - 1 / (2 * Real.pi)) * l T := mul_le_mul_of_nonneg_left hlc₁ hden.le
  have htri : |nuX X τ| ≤ |mu τ| + |PiX X τ| + |PX X τ| := by
    unfold nuX
    calc |mu τ + PiX X τ + PX X τ| ≤ |mu τ + PiX X τ| + |PX X τ| := abs_add_le _ _
      _ ≤ |mu τ| + |PiX X τ| + |PX X τ| := by
          have := abs_add_le (mu τ) (PiX X τ)
          linarith
  calc |nuX X τ| ≤ |mu τ| + |PiX X τ| + |PX X τ| := htri
    _ ≤ (1 / (2 * Real.pi) * l T + (C₁ + 2) + max (Real.log (|τ| / (4 * T))) 0)
        + 3 * Real.sqrt X + Real.sqrt X := by linarith [hμabs, hPiB, hP]
    _ ≤ (l T + 4 * Real.sqrt X) + max (Real.log (|τ| / (4 * T))) 0 := by
        linarith [hslack]
