-- Prove2me | solution 1 for Zeta23.WeilEF.prime_side_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:13:44.07172+00:00
-- url     : https://prove2.me/submissions/6f0abcf7-5397-4458-b705-648a91f1534c

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
import Theorems.Thm_Zeta23_WeilEF_line_integral_swap
import Theorems.Thm_Zeta23_WeilEF_per_n_line_integral

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





/-- On the line Re s = c: H(c+it) = paperFT (tilt k (c − 1/2)) t. -/
theorem Hfn_line (k : ℝ → ℂ) (c t : ℝ) :
    Hfn k (c + t * I) = paperFT (tilt k (c - 1/2)) t := by
  unfold Hfn tilt paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  have harg : I * ((↑c + ↑t * I - 1/2) / I) * ↑u = (((c - 1/2) * u : ℝ) : ℂ) + I * ↑t * ↑u := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    push_cast
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  ring



/-- Step 1 (pointwise on the line): the integrand is the tsum of tilted-transform × L-series
terms.  −ζ'/ζ = LSeries ↗Λ on Re s > 1 (Mathlib), then distribute paperFT (tilt k b) t. -/
theorem integrand_eq_tsum {k : ℝ → ℂ} {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
  have hre : 1 < ((c : ℂ) + t * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simpa using hc1
  have h1 : -logDeriv riemannZeta ((c : ℂ) + t * I) = LSeries (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) := by
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    rw [logDeriv, Pi.div_apply, h2]
    ring
  rw [Hfn_line, h1, LSeries, ← tsum_mul_left]













end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  have h1 : ∀ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := fun t => integrand_eq_tsum hc1 t
  calc (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [line_integral_swap hk hkc hc1]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) :=
        tsum_congr fun n => per_n_line_integral hk hkc n
