-- Prove2me | Definitions.Def_Zeta23_WeilEF_VerticalLine
-- name    : Zeta23_WeilEF_VerticalLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:24:08.360468+00:00
-- url     : https://prove2.me/theorems/5591e142-048d-4a71-8a78-8ddf7236839e
-- title:
--   Vertical-line test function $H$ and the tilted test function $k_b$
-- statement:
--   Two definitions for the vertical-line integrals of the explicit-formula contour, for a test function $k:\mathbb R\to\mathbb C$:
--   - `Hfn k` — the test function on vertical lines, $H(s):=h((s-\tfrac12)/i)$, realised as `paperFT k ((s − 1/2)/I)` where `paperFT` is the paper-convention Fourier transform;
--   - `tilt k b` — the tilted test function
--   $$k_b(u) \;:=\; k(u)\,e^{bu},$$
--   still $C_c^2$ when $k$ is.
--
--   **Role.** These implement the key device by which no contour shifting is needed on the prime side: for $s=c+it$ on a vertical line, $H(s)=\mathrm{paperFT}\,k\,(t-ib)$ with $b:=c-\tfrac12$, and this equals $\mathrm{paperFT}\,k_b\,(t)$ — the transform of the *tilted* function at a real argument. Fourier inversion of $k_b$ (`Zeta23.EF.paper_inversion`) then evaluates the line integral $\frac1{2\pi}\int H(c+it)\,n^{-c-it}\,dt = n^{-c}k_b(\log n)=n^{-1/2}k(\log n)$, and summing against $-\zeta'/\zeta(c+it)=\sum_n\Lambda(n)n^{-c-it}$ (Mathlib's L-series, $1<c$) with a dominated tsum/integral swap produces the prime side of the Weil explicit formula, consumed by the `WeilEF` assembly.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean

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

/-- The test function on vertical lines: H(s) := h((s − 1/2)/i). -/
def Hfn (k : ℝ → ℂ) (s : ℂ) : ℂ := paperFT k ((s - 1/2) / I)

/-- The tilted test function k_b(u) := k(u)·e^{b u}. -/
def tilt (k : ℝ → ℂ) (b : ℝ) : ℝ → ℂ := fun u => k u * (Real.exp (b * u) : ℂ)



















end WeilEF
end Zeta23


