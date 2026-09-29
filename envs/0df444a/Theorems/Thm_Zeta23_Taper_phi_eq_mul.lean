-- Prove2me | Theorems.Thm_Zeta23_Taper_phi_eq_mul
-- name    : Zeta23.Taper.phi_eq_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:28:28.201383+00:00
-- url     : https://prove2.me/theorems/c295b84e-fe63-4bd4-b8e1-c83cb5254184
-- title:
--   Product form of the taper: $\varphi(u) = \varrho\big(\tfrac{L/2-u}{w}\big)\,\varrho\big(\tfrac{L/2+u}{w}\big)$
-- statement:
--   Let $\varrho$ be a taper profile (nondecreasing, $C^3$, $\varrho = 0$ on $(-\infty,0]$, $\varrho = 1$ on $[1,\infty)$) and $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ the taper of [eq:phidef], with $0 < w$ and $2w \le L$.
--
--   The theorem asserts that for every real $u$,
--   $$\varphi(u) \;=\; \varrho\!\left(\frac{L/2-u}{w}\right) \cdot \varrho\!\left(\frac{L/2+u}{w}\right).$$
--   Indeed, for $u \ge 0$ the second factor equals $1$ since $(L/2+u)/w \ge L/(2w) \ge 1$, so the product reduces to $\varrho((L/2-|u|)/w)$; the case $u \le 0$ is symmetric.
--
--   This rewriting eliminates the absolute value $|u|$ from the definition, and is precisely how the project proves $\varphi \in C^3$ (`Zeta23.Taper.phi_contDiff`, its sole consumer): each factor is a $C^3$ function composed with an affine map.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Basic.lean#L147-L158, docstring tag [eq:phidef]

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
variable (ϱ : ℝ → ℝ) (L w : ℝ)
variable {ϱ L w}

theorem Zeta23.Taper.phi_eq_mul (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (u : ℝ) :
    phi ϱ L w u = ϱ ((L / 2 - u) / w) * ϱ ((L / 2 + u) / w) := by sorry
