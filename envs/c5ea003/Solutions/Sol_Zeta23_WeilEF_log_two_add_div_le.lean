-- Prove2me | solution 1 for Zeta23.WeilEF.log_two_add_div_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:05:22.776015+00:00
-- url     : https://prove2.me/submissions/d7ff1fce-32e2-43aa-856e-ace559444e5d

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





















end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 + x) / (1 + x ^ 2) ≤ 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have h1 := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 + x by linarith) (show (0:ℝ) < 1/2 by norm_num)
  have h2 : (2 + x) ^ (1 / 2 : ℝ) ≤ (3 / 2) * (1 + x) ^ (1 / 2 : ℝ) := by
    have : (2 + x) ^ (1 / 2 : ℝ) ≤ ((9/4) * (1 + x)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at this
    rw [show ((9:ℝ)/4) ^ (1/2:ℝ) = 3/2 by
      rw [show (9:ℝ)/4 = (3/2) ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num] at this
    exact this
  have hlog : Real.log (2 + x) ≤ 3 * (1 + x) ^ (1 / 2 : ℝ) := by
    have : (2 + x) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (2 + x) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1; linarith
  have hsq : 1 / (1 + x ^ 2) ≤ 2 * (1 + x) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, div_le_iff₀ (by positivity)]
    rw [show 2 * ((1 + x) ^ 2)⁻¹ * (1 + x ^ 2) = 2 * (1 + x ^ 2) / (1 + x) ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - 1)]
  have h0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  calc Real.log (2 + x) / (1 + x ^ 2) = Real.log (2 + x) * (1 / (1 + x ^ 2)) := by ring
    _ ≤ (3 * (1 + x) ^ (1 / 2 : ℝ)) * (2 * (1 + x) ^ (-2 : ℝ)) :=
        mul_le_mul hlog hsq (by positivity) (by positivity)
    _ = 6 * ((1 + x) ^ (1 / 2 : ℝ) * (1 + x) ^ (-2 : ℝ)) := by ring
    _ = 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add (by linarith)]; norm_num
