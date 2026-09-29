-- Prove2me | Theorems.Thm_Zeta23_RvM_horizontal_fold
-- name    : Zeta23.RvM.horizontal_fold
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:10.608935+00:00
-- url     : https://prove2.me/theorems/3094f4c6-a051-4bde-887d-41ce331b4d38
-- title:
--   Horizontal fold: $\int_{-1}^{2} \frac{\Lambda'}{\Lambda}(\sigma+iT)\,d\sigma = 2i\,\mathrm{Im}\int_{1/2}^{2}\frac{\Lambda'}{\Lambda}(\sigma+iT)\,d\sigma$
-- statement:
--   **Setup.** $\Lambda$ is the completed Riemann zeta function (Mathlib's `completedRiemannZeta`), satisfying the functional equation $\Lambda(s) = \Lambda(1-s)$ and the reflection $\Lambda(\bar s) = \overline{\Lambda(s)}$. $T$ is a *good height* (`GoodHeight T`): no nontrivial zero of $\zeta$ has ordinate $T$.
--
--   **Statement.** For every good height $T \ge 1$,
--
--   $$\int_{-1}^{2} \frac{\Lambda'}{\Lambda}(\sigma + iT)\, d\sigma \;=\; 2i \cdot \mathrm{Im} \int_{1/2}^{2} \frac{\Lambda'}{\Lambda}(\sigma + iT)\, d\sigma,$$
--
--   the right-hand imaginary part being coerced back into $\mathbb{C}$. The two symmetries of $\Lambda$ combine to the relation $\frac{\Lambda'}{\Lambda}(1 - \bar s) = \overline{\frac{\Lambda'}{\Lambda}(s)}\cdot(-1)$, which maps the segment $\sigma \in [-1, 1/2]$ at height $T$ onto $\sigma \in [1/2, 2]$: the real parts of the two halves cancel and the imaginary parts double.
--
--   **Role.** In `Zeta23.RvM.Fold` this halves the horizontal sides of the argument-principle rectangle for the zero count $N(T_1, T_2)$, reducing them to the half-contour on which Backlund's bound applies. Consumed by `Zeta23.RvM.rectangleIntegral_logDeriv_completedZeta_eq_halfContour`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/Fold.lean#L108-L143

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
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory Set intervalIntegral
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.horizontal_fold {T : ℝ} (hT : 1 ≤ T) (hgood : GoodHeight T) :
    ∫ σ in (-1 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)
      = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)).im : ℂ) := by sorry
