-- Prove2me | solution 1 for Zeta23.WeilEF.vertical_line_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:01:19.892191+00:00
-- url     : https://prove2.me/submissions/44911f0a-9409-4ed8-a8e1-3583dae79709

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













/-- continuity ⇒ integrability on vertical lines under a majorant (used by vertical_line_shift). -/
lemma integrable_line {f : ℂ → ℂ} {σ : ℝ} (hf : ∀ t : ℝ, DifferentiableAt ℂ f (σ + t * I))
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hb : ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ φ t) :
    Integrable (fun t : ℝ => f (σ + t * I)) := by
  have hc : Continuous (fun t : ℝ => f (σ + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hg : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
    show ContinuousAt (f ∘ fun t : ℝ => (σ : ℂ) + t * I) t
    exact ContinuousAt.comp_of_eq (hf t).continuousAt hg.continuousAt rfl
  exact hφ.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)








end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hbound : ∀ (σ t : ℝ), a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ φ t)
    (hφtop : Filter.Tendsto φ Filter.atTop (nhds 0))
    (hφbot : Filter.Tendsto φ Filter.atBot (nhds 0)) :
    ∫ t : ℝ, f (b + t * I) = ∫ t : ℝ, f (a + t * I) := by
  -- integrability on the vertical lines
  have hint : ∀ σ : ℝ, a ≤ σ → σ ≤ b → Integrable (fun t : ℝ => f (σ + t * I)) := fun σ h1 h2 =>
    integrable_line (fun t => hf _ (by simp [h1]) (by simp [h2])) hφ (fun t => hbound σ t h1 h2)
  have hφnn : ∀ t, 0 ≤ φ t := fun t => (norm_nonneg _).trans (hbound a t le_rfl hab)
  -- Cauchy on the rectangles [a,b] × [−R, R]
  have hrect : ∀ R : ℝ, (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))
      = -I * ((∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I))) := by
    intro R
    have hdiff : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-R) R) := by
      intro z hz
      rw [Set.uIcc_of_le hab] at hz
      exact (hf z hz.1.1 hz.1.2).differentiableWithinAt
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) (by simpa using hdiff)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, smul_eq_mul] at H
    have key : I * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)))
        = (∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I)) := by
      push_cast at H ⊢
      linear_combination H
    calc (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))
        = -(I * I) * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))) := by
          rw [I_mul_I]; ring
      _ = -I * (I * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)))) := by
          ring
      _ = _ := by rw [key]
  -- the horizontal sides are small
  have hsmall : ∀ R : ℝ, ‖(∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))‖
      ≤ (b - a) * (φ R + φ (-R)) := by
    intro R
    rw [hrect R, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have h1 : ‖∫ x in a..b, f (x + R * I)‖ ≤ φ R * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact hbound x R hx.1.le hx.2
    have h2 : ‖∫ x in a..b, f (x + (-R) * I)‖ ≤ φ (-R) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        have := hbound x (-R) hx.1.le hx.2
        simpa using this
    rw [abs_of_nonneg (by linarith)] at h1 h2
    calc ‖(∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I))‖
        ≤ ‖∫ x in a..b, f (x + R * I)‖ + ‖∫ x in a..b, f (x + (-R) * I)‖ := norm_sub_le _ _
      _ ≤ φ R * (b - a) + φ (-R) * (b - a) := add_le_add h1 h2
      _ = (b - a) * (φ R + φ (-R)) := by ring
  -- limits
  set g : ℝ → ℂ := fun R => (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)) with hg
  have hlim1 : Filter.Tendsto g Filter.atTop (nhds ((∫ t : ℝ, f (b + t * I)) - (∫ t : ℝ, f (a + t * I)))) := by
    apply Filter.Tendsto.sub
    · exact intervalIntegral_tendsto_integral (hint b hab le_rfl) Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
    · exact intervalIntegral_tendsto_integral (hint a le_rfl hab) Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hlim0 : Filter.Tendsto g Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun R => norm_nonneg _) (fun R => hsmall R) ?_
    have : Filter.Tendsto (fun R => (b - a) * (φ R + φ (-R))) Filter.atTop (nhds ((b - a) * (0 + 0))) :=
      (hφtop.add (hφbot.comp Filter.tendsto_neg_atTop_atBot)).const_mul _
    simpa using this
  have := tendsto_nhds_unique hlim1 hlim0
  exact sub_eq_zero.mp this
