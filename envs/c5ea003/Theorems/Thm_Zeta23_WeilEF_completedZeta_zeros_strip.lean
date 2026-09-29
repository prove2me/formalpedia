-- Prove2me | Theorems.Thm_Zeta23_WeilEF_completedZeta_zeros_strip
-- name    : Zeta23.WeilEF.completedZeta_zeros_strip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:48:37.703859+00:00
-- url     : https://prove2.me/theorems/3f362ad6-dde5-493f-95f3-923f01a4db5e
-- title:
--   In the open critical strip, zeros of $\Lambda$ are the nontrivial zeros of $\zeta$, with equal order
-- statement:
--   Let $\Lambda$ be the completed Riemann zeta function $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$ (Mathlib's `completedRiemannZeta`), and recall that $\rho$ is called a nontrivial zero of $\zeta$ (the project's `IsNontrivialZero`) when $\zeta(\rho) = 0$ and $0 < \operatorname{Re}\rho < 1$.
--
--   For every $\rho \in \mathbb{C}$ with $0 < \operatorname{Re}\rho < 1$, both of the following hold:
--   $$\Lambda(\rho) = 0 \;\Longleftrightarrow\; \rho \text{ is a nontrivial zero of } \zeta,$$
--   and the analytic vanishing orders agree,
--   $$\operatorname{ord}_{\rho}\Lambda = \operatorname{ord}_{\rho}\zeta,$$
--   where the order is Mathlib's `analyticOrderAt` (valued in $\mathbb{N}\cup\{\infty\}$). The point is that the Archimedean factor $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ is analytic and nonvanishing in the open strip, so it changes neither the zero set nor the multiplicities there.
--
--   This identification is used by `completedZeta_ne_zero_on_horizontals` to transfer nonvanishing of $\zeta$ on horizontal segments to nonvanishing of $\Lambda$, as part of the contour-shift argument for the Weil explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/XiLogDeriv.lean#L93-L115

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
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement

open Zeta23
open Complex Filter Topology

theorem Zeta23.WeilEF.completedZeta_zeros_strip {ρ : ℂ} (h : 0 < ρ.re) (h' : ρ.re < 1) :
    (completedRiemannZeta ρ = 0 ↔ IsNontrivialZero ρ) ∧
    analyticOrderAt completedRiemannZeta ρ = analyticOrderAt riemannZeta ρ := by sorry
