-- Prove2me | Theorems.Thm_Zeta23_RvM_rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount
-- name    : Zeta23.RvM.rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:31.812446+00:00
-- url     : https://prove2.me/theorems/3cc88695-0014-4fa5-8699-3095f4e72285
-- title:
--   $N(T_1, T_2)$ as a contour integral: $\frac{1}{2\pi i}\oint_{\partial R} \frac{\Lambda'}{\Lambda} = N(T_1, T_2)$
-- statement:
--   **Setup.** $\Lambda$ is the completed Riemann zeta function (Mathlib's `completedRiemannZeta`). `RectangleIntegral' f z w` denotes $\frac{1}{2\pi i}$ times the counterclockwise boundary integral of $f$ over the axis-parallel rectangle with opposite corners $z$ and $w$; here the rectangle is $[-1, 2] \times [T_1, T_2]$, with corners $-1 + iT_1$ and $2 + iT_2$. The count $N(T_1, T_2)$ (`Ncount`) is the number of nontrivial zeros $\rho$ of $\zeta$ (i.e. $\zeta(\rho) = 0$, $0 < \mathrm{Re}\,\rho < 1$) with $T_1 < \mathrm{Im}\,\rho \le T_2$, counted with multiplicity: $N(T_1,T_2) = \sum_{\rho} m_\rho$ with $m_\rho$ the order of vanishing of $\zeta$ at $\rho$.
--
--   **Statement.** Let $0 < T_1 \le T_2$, and suppose no nontrivial zero of $\zeta$ has ordinate exactly $T_1$ or exactly $T_2$. Then
--
--   $$\frac{1}{2\pi i} \oint_{\partial\, ([-1,2] \times [T_1, T_2])} \frac{\Lambda'}{\Lambda}(s)\, ds \;=\; N(T_1, T_2),$$
--
--   the right-hand side read as a complex number. This is the argument principle for $\Lambda$, whose zeros inside the rectangle are exactly the nontrivial zeros of $\zeta$ with ordinate in $(T_1, T_2]$ (via `Zeta23.RvM.completedRiemannZeta_eq_zero_iff`), $\Lambda$ having no poles there in Mathlib's normalization.
--
--   **Role.** The exact starting identity of the Riemann–von Mangoldt formula in `Zeta23.RvM.CountByIntegral`: `Zeta23.RvM.rvM_main_param` splits this contour integral into the $\Gamma$-side main term $\int_{T_1}^{T_2}\mu$ and the $O(\log T)$ zeta-side remainder.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/CountByIntegral.lean#L96-L162

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
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement

open Complex Set Topology Filter Real
open Zeta23

theorem Zeta23.RvM.rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = (Ncount T₁ T₂ : ℂ) := by sorry
