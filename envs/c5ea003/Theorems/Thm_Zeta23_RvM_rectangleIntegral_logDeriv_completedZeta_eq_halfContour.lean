-- Prove2me | Theorems.Thm_Zeta23_RvM_rectangleIntegral_logDeriv_completedZeta_eq_halfContour
-- name    : Zeta23.RvM.rectangleIntegral_logDeriv_completedZeta_eq_halfContour
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:44.559534+00:00
-- url     : https://prove2.me/theorems/4cec908c-bcf2-4d7e-bc5a-887c52f3ff06
-- title:
--   The fold: rectangle integral of $\Lambda'/\Lambda$ equals $2i\,\operatorname{Im}$ of the right half-contour
-- statement:
--   Let $\Lambda$ denote the completed Riemann zeta function (Mathlib's `completedRiemannZeta`), and let $\Lambda'/\Lambda$ be its logarithmic derivative. A height $T$ is a *good height* (`GoodHeight T`) if no nontrivial zero of $\zeta$ has imaginary part equal to $T$. For a function $F$ the *right half-contour* integral is
--   $$\mathrm{halfContour}(F, T_1, T_2) \;=\; \int_{1/2}^{2} F(\sigma + iT_1)\,d\sigma \;+\; i\int_{T_1}^{T_2} F(2 + it)\,dt \;-\; \int_{1/2}^{2} F(\sigma + iT_2)\,d\sigma,$$
--   i.e. the piecewise-linear path $\tfrac12 + iT_1 \to 2 + iT_1 \to 2 + iT_2 \to \tfrac12 + iT_2$. `RectangleIntegral F z w` is the counterclockwise contour integral over the boundary of the axis-parallel rectangle with opposite corners $z$ and $w$ (bottom side plus right side minus top side minus left side).
--
--   **Statement.** For all real $T_1, T_2$ with $1 \le T_1 < T_2$, both good heights,
--   $$\oint_{\partial([-1,2]\times[T_1,T_2])} \frac{\Lambda'}{\Lambda}(s)\,ds \;=\; 2i \cdot \operatorname{Im}\bigl(\mathrm{halfContour}(\Lambda'/\Lambda,\, T_1,\, T_2)\bigr),$$
--   where the rectangle has corners $-1 + iT_1$ and $2 + iT_2$.
--
--   This is the classical "folding" step of the Riemann-von Mangoldt argument: the functional-equation symmetry $\Lambda(s) = \Lambda(1-s)$ together with reflection in the real axis collapses the full rectangular contour around the critical strip to twice the imaginary part of its right half. It is consumed by `Zeta23.RvM.rvM_main_param`, the parametric main term of the zero-counting formula $N(T,2T)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Fold.lean#L164-L185

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory Set intervalIntegral
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.rectangleIntegral_logDeriv_completedZeta_eq_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁)
    (h12 : T₁ < T₂) (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    RectangleIntegral (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℂ) := by sorry
