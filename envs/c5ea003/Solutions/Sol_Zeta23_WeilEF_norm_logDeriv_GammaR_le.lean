-- Prove2me | solution 1 for Zeta23.WeilEF.norm_logDeriv_GammaR_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:18:09.406539+00:00
-- url     : https://prove2.me/submissions/44733b81-22e7-487f-bae4-1a66da241477

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
import Theorems.Thm_Zeta23_WeilEF_digamma_growth_strip
import Theorems.Thm_Zeta23_WeilEF_logDeriv_GammaR

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

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
    ‖logDeriv Complex.Gammaℝ (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC, hψ⟩ := digamma_growth_strip
  have hlogπ0 : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨2 * Real.log Real.pi + C, by positivity, ?_⟩
  intro σ t h1 h2
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [logDeriv_GammaR hre]
  have hs2 : ((σ : ℂ) + t * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hψb := hψ (((σ : ℂ) + t * I) / 2) (by rw [hs2]; simp; linarith) (by rw [hs2]; simp; linarith)
  have him : (((σ : ℂ) + t * I) / 2).im = t / 2 := by rw [hs2]; simp
  rw [him] at hψb
  have hlog2 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog2' : (1:ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hloght : Real.log (2 + |t / 2|) ≤ Real.log (2 + |t|) := by
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_two]; linarith [abs_nonneg t]
  have hlogπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  calc ‖-((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖
      ≤ ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ + ‖1 / 2 * Complex.digamma (((σ : ℂ) + t * I) / 2)‖ :=
        norm_add_le _ _
    _ = Real.log Real.pi / 2 + (1 / 2) * ‖Complex.digamma (((σ : ℂ) + t * I) / 2)‖ := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogπ, norm_mul]
        norm_num
    _ ≤ Real.log Real.pi / 2 + (1 / 2) * (C * Real.log (2 + |t / 2|)) := by gcongr
    _ ≤ Real.log Real.pi * Real.log (2 + |t|) * 2 + C * Real.log (2 + |t|) := by
        nlinarith [hC.le, hloght, Real.log_nonneg (show (1:ℝ) ≤ 2 + |t/2| by linarith [abs_nonneg (t/2)])]
    _ = (2 * Real.log Real.pi + C) * Real.log (2 + |t|) := by ring
