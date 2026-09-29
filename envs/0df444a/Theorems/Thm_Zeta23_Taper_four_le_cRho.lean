-- Prove2me | Theorems.Thm_Zeta23_Taper_four_le_cRho
-- name    : Zeta23.Taper.four_le_cRho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:32:38.441713+00:00
-- url     : https://prove2.me/theorems/39868755-e6fe-4230-bce7-464b8b7b9f87
-- title:
--   Lower bound for the profile constant: $c_\varrho \ge 4$
-- statement:
--   Let $\varrho$ be a taper profile (`TaperProfile`): a monotone $C^3$ function equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. Its profile constant is $c_\varrho = 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$ (`cRho`), as in [eq:phinorms].
--
--   Then
--
--   $$4 \le c_\varrho,$$
--
--   the parenthetical \"$(\ge 4)$\" of [eq:phinorms]: since $\varrho$ climbs from $0$ to $1$ on $[0,1]$, its derivative must reach size $1$ somewhere, so $\|\varrho'\|_\infty \ge 1$.
--
--   This lower bound keeps the envelope $\psi$ and the various $c_\varrho/w$ estimates uniform; it is used throughout the Taper modules (positivity and integrability of $\psi$, the $\psi$-integrals, the second-moment bounds for $\hat\varphi$ and $\Phi$) and in `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L477-L494, docstring tag [eq:phinorms]

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

theorem Zeta23.Taper.four_le_cRho (hϱ : TaperProfile ϱ) : 4 ≤ cRho ϱ := by sorry
