-- Prove2me | Theorems.Thm_Zeta23_RvM_vertical_fold
-- name    : Zeta23.RvM.vertical_fold
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:28.960789+00:00
-- url     : https://prove2.me/theorems/ff696bfc-ef23-49b1-88bd-cfdf7bfc4926
-- title:
--   Vertical fold: $\int \Lambda'/\Lambda(-1+it)\,dt = -\overline{\int \Lambda'/\Lambda(2+it)\,dt}$
-- statement:
--   Let $\Lambda$ be the completed Riemann zeta function (`completedRiemannZeta`) and $\Lambda'/\Lambda$ its logarithmic derivative. For all real $T_1, T_2$ with $1 \le T_1 \le T_2$,
--   $$\int_{T_1}^{T_2} \frac{\Lambda'}{\Lambda}(-1 + it)\,dt \;=\; -\,\overline{\int_{T_1}^{T_2} \frac{\Lambda'}{\Lambda}(2 + it)\,dt},$$
--   where the bar denotes complex conjugation (`starRingEnd` $\mathbb{C}$).
--
--   This identity combines the functional equation $\Lambda(s) = \Lambda(1-s)$ (which relates the line $\operatorname{Re} s = -1$ to the line $\operatorname{Re} s = 2$) with the reflection symmetry $\overline{\Lambda(\bar s)} = \Lambda(s)$. It is the reason the left vertical side of the zero-counting rectangle can be folded onto the right one.
--
--   Its sole consumer is `Zeta23.RvM.rectangleIntegral_logDeriv_completedZeta_eq_halfContour`, the fold identity expressing the full rectangle integral of $\Lambda'/\Lambda$ as $2i$ times the imaginary part of the right half-contour.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Fold.lean#L145-L162

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

open Complex MeasureTheory Set intervalIntegral

theorem Zeta23.RvM.vertical_fold {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, logDeriv completedRiemannZeta (-1 + t * I)
      = -starRingEnd ℂ (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) := by sorry
