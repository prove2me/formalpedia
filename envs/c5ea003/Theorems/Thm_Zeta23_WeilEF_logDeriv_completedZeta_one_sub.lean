-- Prove2me | Theorems.Thm_Zeta23_WeilEF_logDeriv_completedZeta_one_sub
-- name    : Zeta23.WeilEF.logDeriv_completedZeta_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:38.758575+00:00
-- url     : https://prove2.me/theorems/18ccadbd-14ac-4e19-b6c6-76674e07aad1
-- title:
--   Functional equation for the logarithmic derivative: $\Lambda'/\Lambda(1-s) = -\Lambda'/\Lambda(s)$
-- statement:
--   Let $\Lambda$ denote the completed Riemann zeta function (Mathlib's `completedRiemannZeta`), which satisfies the functional equation $\Lambda(1-s) = \Lambda(s)$, and write $\operatorname{logDeriv}\Lambda = \Lambda'/\Lambda$.
--
--   For every $s \in \mathbb{C}$ with $s \ne 0$ and $s \ne 1$ (avoiding the two poles of $\Lambda$),
--   $$\frac{\Lambda'}{\Lambda}(1 - s) \;=\; -\,\frac{\Lambda'}{\Lambda}(s).$$
--   This is obtained by differentiating the functional equation: the chain rule applied to $\Lambda(1-s) = \Lambda(s)$ flips the sign of the logarithmic derivative.
--
--   This antisymmetry is what lets the project fold the two vertical lines $\operatorname{Re} s = c$ and $\operatorname{Re} s = 1 - c$ into a single integral: it is consumed by `horizontal_vanish` and `verticals_eq` in the Weil explicit-formula development, and by `horizontal_fold` and `vertical_fold` in the Riemann-von Mangoldt zero-counting argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/XiLogDeriv.lean#L77-L91

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex Filter Topology

theorem Zeta23.WeilEF.logDeriv_completedZeta_one_sub (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by sorry
