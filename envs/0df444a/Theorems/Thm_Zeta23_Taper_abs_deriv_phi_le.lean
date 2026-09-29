-- Prove2me | Theorems.Thm_Zeta23_Taper_abs_deriv_phi_le
-- name    : Zeta23.Taper.abs_deriv_phi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:29.440462+00:00
-- url     : https://prove2.me/theorems/0e6ee2e3-5343-4b82-bd7c-42cfb521b674
-- title:
--   Derivative bound for the taper: $\|\varphi'\|_\infty \le \|\varrho'\|_\infty / w$
-- statement:
--   **Setup.** Let $\varrho$ be a taper profile ($C^3$, monotone, $0$ on $(-\infty,0]$, $1$ on $[1,\infty)$) and $\varphi(u) := \varrho\bigl((L/2 - |u|)/w\bigr)$ the taper of [eq:phidef], with ramp width $w > 0$ and $2w \le L$. Write `supDeriv ϱ` $:= \sup_{x}|\varrho'(x)| = \|\varrho'\|_\infty$ (finite since $\varrho'$ is continuous with support in $[0,1]$).
--
--   **Statement.** For every real $u$,
--   $$\bigl|\varphi'(u)\bigr| \;\le\; \frac{\|\varrho'\|_\infty}{w},$$
--   where $\varphi'$ is Lean's `deriv` of $\varphi$. This is [eq:phinorms], "$\|\varphi'\|_\infty = \|\varrho'\|_\infty / w$", recorded as the inequality $\le$, which is all that is used; the chain rule contributes the factor $1/w$ from the ramp rescaling, and the value at the corner $u = 0$ is handled via oddness of $\varphi'$ (both one-sided values vanish there since $\varphi \equiv 1$ near $0$ when $2w \le L$).
--
--   **Role.** Consumed by `Zeta23.Taper.integral_abs_deriv2_phi_sq_le` in `Zeta23.Taper.Norms`: the bound on $\|(\varphi^2)''\|_1$ (and hence the constant $c_\varrho$ governing the decay of $\Phi$) is assembled from $\|\varphi'\|_\infty$ and $\|\varphi''\|_1$ via $(\varphi^2)'' = 2(\varphi')^2 + 2\varphi\varphi''$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L233-L255, docstring tag [eq:phinorms]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.abs_deriv_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) (u : ℝ) :
    |deriv (phi ϱ L w) u| ≤ supDeriv ϱ / w := by sorry
