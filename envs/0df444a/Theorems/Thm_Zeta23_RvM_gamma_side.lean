-- Prove2me | Theorems.Thm_Zeta23_RvM_gamma_side
-- name    : Zeta23.RvM.gamma_side
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:39:26.928602+00:00
-- url     : https://prove2.me/theorems/297029ce-73a7-484c-9b68-5e9fb9fa7f29
-- title:
--   The $\Gamma$-side identity: $\frac{1}{\pi}\,\mathrm{Im}\,\mathrm{halfContour}(\Gamma_{\mathbb R}'/\Gamma_{\mathbb R}) = \int_{T_1}^{T_2}\mu$
-- statement:
--   **Setup.** $\Gamma_{\mathbb R}(s) = \pi^{-s/2}\Gamma(s/2)$ is the archimedean factor (Mathlib's `Complex.Gammaℝ`). For a function $F$, `halfContour F T₁ T₂` is the integral of $F$ along the right half-contour $\tfrac12 + iT_1 \to 2 + iT_1 \to 2 + iT_2 \to \tfrac12 + iT_2$, i.e. $\int_{1/2}^{2} F(\sigma + iT_1)\,d\sigma + i\int_{T_1}^{T_2} F(2 + it)\,dt - \int_{1/2}^{2} F(\sigma + iT_2)\,d\sigma$. The density $\mu$ is defined by $\mu(\tau) = \frac{1}{2\pi}\,\mathrm{Re}\,\psi\bigl(\tfrac14 + \tfrac{i\tau}{2}\bigr) - \frac{\log \pi}{2\pi}$ [eq:mudef], where $\psi = \Gamma'/\Gamma$ is the digamma function.
--
--   **Statement.** For all real $T_1, T_2$ with $0 < T_1$ and $0 < T_2$,
--
--   $$\frac{1}{\pi}\,\mathrm{Im}\ \mathrm{halfContour}\Bigl(\frac{\Gamma_{\mathbb R}'}{\Gamma_{\mathbb R}},\, T_1,\, T_2\Bigr) \;=\; \int_{T_1}^{T_2} \mu(t)\, dt.$$
--
--   The proof runs Cauchy–Goursat for $\log$-derivative of $\Gamma_{\mathbb R}$ on the rectangle $[1/2, 2] \times [T_1, T_2]$ (where $\Gamma_{\mathbb R}$ is analytic and nonvanishing) to move the half-contour onto the critical line, where $\mathrm{Re}\,(\Gamma_{\mathbb R}'/\Gamma_{\mathbb R})(\tfrac12 + it) = \pi\,\mu(t)$.
--
--   **Role.** Step (M4) of the Riemann–von Mangoldt main-term computation in `Zeta23.RvM.GammaSide`: it produces the smooth main term $\int \mu$ of the zero-counting formula. Consumed by `Zeta23.RvM.rvM_main_param`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/GammaSide.lean#L119-L156

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory Set
open scoped Interval
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.gamma_side {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im = ∫ t in T₁..T₂, mu t := by sorry
