-- Prove2me | Theorems.Thm_Zeta23_Taper_abs_le_psi_of_bounds
-- name    : Zeta23.Taper.abs_le_psi_of_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:31:36.869929+00:00
-- url     : https://prove2.me/theorems/57e6c312-1864-4755-8197-6613703eb0f6
-- title:
--   Three pointwise bounds imply the envelope bound $|F| \le \psi$
-- statement:
--   Let $w > 0$, and let $\psi$ be the decay envelope of [eq:psidef], defined for real $r$ by $\psi(r) = \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ with the convention $\psi(0) = L$ (made explicit in Lean because $2/0 = 0$ there). The profile constant is $c_\varrho = 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$ (`cRho`).
--
--   Suppose $F : \mathbb{R} \to \mathbb{R}$ satisfies the three bounds
--
--   $$|F(r)| \le L, \qquad |F(r)|\,|r| \le 2, \qquad |F(r)|\,r^2 \le c_\varrho/w \quad (r \in \mathbb{R}).$$
--
--   Then $|F(r)| \le \psi(r)$ for every real $r$.
--
--   This is the abstract form of [eq:psidef]: it packages the three decay estimates for $\hat\varphi$ into the single envelope $\psi$, and is consumed by `Zeta23.PrimeSide.localHyps_concrete`, which verifies the concrete local hypotheses on the prime side of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L365-L377, docstring tag [eq:psidef]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
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

theorem Zeta23.Taper.abs_le_psi_of_bounds (hw : 0 < w) {F : ℝ → ℝ} (h0 : ∀ r, |F r| ≤ L)
    (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ cRho ϱ / w) (r : ℝ) :
    |F r| ≤ psi ϱ L w r := by sorry
