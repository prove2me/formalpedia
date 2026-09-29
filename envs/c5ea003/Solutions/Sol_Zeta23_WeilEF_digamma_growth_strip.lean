-- Prove2me | solution 1 for Zeta23.WeilEF.digamma_growth_strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:31:45.91701+00:00
-- url     : https://prove2.me/submissions/1cc33c99-0e21-4f6d-9530-986e6ffe2564

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Theorems.Thm_Zeta23_StirlingVert_digamma_stirling

-- from Zeta23.WeilEF.VerticalLine
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/VerticalLine.lean.  Vertical-line integrals for the EF contour.

KEY DEVICE (no contour shifting needed on the prime side): for s = c + it on a vertical line,
H(s) := h((s−1/2)/i) = paperFT k (t − i·b) with b := c − 1/2, and
  paperFT k (t − i·b) = paperFT k_b t,  where k_b(u) := k(u)·e^{b·u}  (the TILTED test function,
still C_c²).  Hence the line integral (1/2π)∫ H(c+it)·n^{−c−it} dt is, by Fourier inversion of
k_b (Zeta23.EF.paper_inversion, proved in Zeta23/ExplicitFormula.lean, with integrability from
Zeta23/ExplicitFormula/Bridge.lean's integrable_fourier_of_contDiff_two),
  n^{−c}·k_b(log n) = n^{−c}·k(log n)·n^{b} = n^{−1/2}·k(log n).
Summing against −ζ'/ζ(c+it) = Σ Λ(n)n^{−c−it} (Mathlib LSeries, 1 < c) with a dominated
tsum/integral swap (domination: ‖paperFT k_b t‖(1+t²) ≤ ‖k_b‖₁+‖k_b''‖₁ from
Zeta23.EF.norm_paperFT_mul_one_add_sq_le × Σ Λ(n)n^{−c} < ∞) gives the prime side.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex MeasureTheory
open scoped ArithmeticFunction





















end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 1 →
    ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  -- differentiability of ψ on the right half-plane
  have hdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.digamma s := by
    intro s hs
    have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      rw [h] at hs
      simp only [Complex.neg_re, Complex.natCast_re] at hs
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hΓan : AnalyticAt ℂ Complex.Gamma s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hopen.mem_nhds hs] with w hw
      refine Complex.differentiableAt_Gamma w fun m => ?_
      intro h
      rw [h] at hw
      simp only [Complex.neg_re, Complex.natCast_re] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
    have hψan : AnalyticAt ℂ Complex.digamma s := by
      have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := hΓan.deriv
      have h2 := h1.div hΓan hΓne
      exact h2.congr (by
        filter_upwards with w
        rw [Complex.digamma_def, logDeriv_apply]
        rfl)
    exact hψan.differentiableAt
  -- bound on the compact rectangle |Im| ≤ 1/2
  have hK : IsCompact (Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2))) := by
    intro s hs
    have hsre : 1/4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact ((hdiff s (by linarith)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcontK
  have hM0 : (0 : ℝ) ≤ M := by
    have h := hM (1/2 : ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re, Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im, Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have hK₀0 : (0 : ℝ) < K₀ := by positivity
  refine ⟨max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1, by positivity, fun s hre1 hre2 => ?_⟩
  have hlogmono : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    have := abs_nonneg s.im
    linarith
  have hlogpos : (0 : ℝ) < Real.log (2 + |s.im|) := lt_of_lt_of_le hlog2 hlogmono
  rcases le_or_gt (|s.im|) (1/2) with him | him
  · -- compact part
    have hsK : s ∈ Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨hre1, hre2⟩, ?_⟩
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le s.im]; linarith [le_abs_self s.im]]
    calc ‖Complex.digamma s‖ ≤ M := hM s hsK
      _ = (M / Real.log 2) * Real.log 2 := by
          field_simp
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul ?_ hlogmono hlog2.le (by positivity)
          calc M / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) := le_max_left _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
  · -- Stirling part: ‖ψ‖ ≤ ‖ψ − log s + (1/2)/s‖ + ‖log s‖ + ‖(1/2)/s‖
    have hsre0 : (0 : ℝ) < s.re := by linarith
    have hst := Zeta23.StirlingVert.digamma_stirling (w := s) hsre0 (by linarith)
    have hsnorm_lo : (1/4 : ℝ) ≤ ‖s‖ :=
      le_trans hre1 (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have hsnorm0 : (0 : ℝ) < ‖s‖ := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsnorm0
      exact lt_irrefl 0 hsnorm0
    have hsnorm_hi : ‖s‖ ≤ 1 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 1 + |s.im| := by
            have : |s.re| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    -- ‖log s‖ ≤ |log ‖s‖| + π ≤ (log 4 + log(2+|im|)) + π
    have hlog_s : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + Real.pi := by
      calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖s‖| + Real.pi := by
            rw [Complex.log_re, Complex.log_im]
            have := Complex.abs_arg_le_pi s
            linarith [abs_nonneg (Complex.arg s)]
    have hlog_abs : |Real.log ‖s‖| ≤ Real.log 4 + Real.log (2 + |s.im|) := by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · -- ‖s‖ ≤ 1-ish: |log| = −log ≤ log 4 since ‖s‖ ≥ 1/4
        have h1 : Real.log (1/4 : ℝ) ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hsnorm_lo
        have h2 : Real.log (1/4 : ℝ) = -Real.log 4 := by
          rw [show (1/4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := by
          apply Real.log_nonneg
          have := abs_nonneg s.im
          linarith
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖s‖ ≤ Real.log (2 + |s.im|) := by
          apply Real.log_le_log hsnorm0
          have := abs_nonneg s.im
          linarith
        have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
    have hinv_s : ‖(1/2 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by
        rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [h1, div_le_iff₀ hsnorm0]
      linarith
    have him2 : 3 / s.im ^ 2 ≤ 12 := by
      have h1 : (1/4 : ℝ) ≤ s.im ^ 2 := by
        have h2 : (1/2 : ℝ) ≤ |s.im| := him.le
        nlinarith [abs_nonneg s.im, sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have htot : ‖Complex.digamma s‖
        ≤ Real.log (2 + |s.im|) + K₀ := by
      have h1 : ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := by
        have h2 : Complex.digamma s = (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
            + Complex.log s - (1/2 : ℂ) / s := by ring
        calc ‖Complex.digamma s‖
            = ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                + Complex.log s - (1/2 : ℂ) / s‖ := by rw [← h2]
          _ ≤ ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s) + Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := norm_sub_le _ _
          _ ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := by
              have := norm_add_le (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                (Complex.log s)
              linarith
      rw [hK₀]
      have hπ4 : Real.pi < 4 := Real.pi_lt_four
      calc ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := h1
        _ ≤ 3 / s.im ^ 2 + (|Real.log ‖s‖| + Real.pi) + 2 := by
            have := hst
            linarith [hlog_s, hinv_s]
        _ ≤ 12 + ((Real.log 4 + Real.log (2 + |s.im|)) + Real.pi) + 2 := by
            linarith [him2, hlog_abs]
        _ ≤ Real.log (2 + |s.im|) + (14 + Real.pi + Real.log 4) := by linarith
    calc ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := htot
      _ ≤ Real.log (2 + |s.im|) + (K₀ / Real.log 2) * Real.log (2 + |s.im|) := by
          have h3 : K₀ / Real.log 2 * Real.log 2 ≤ K₀ / Real.log 2 * Real.log (2 + |s.im|) :=
            mul_le_mul_of_nonneg_left hlogmono (by positivity)
          have h4 : K₀ / Real.log 2 * Real.log 2 = K₀ := by field_simp
          linarith
      _ = (1 + K₀ / Real.log 2) * Real.log (2 + |s.im|) := by ring
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul_of_nonneg_right ?_ hlogpos.le
          calc (1 + K₀ / Real.log 2) ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
                le_max_right _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
