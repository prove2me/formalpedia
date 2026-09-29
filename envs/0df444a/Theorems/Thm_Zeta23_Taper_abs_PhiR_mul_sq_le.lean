-- Prove2me | Theorems.Thm_Zeta23_Taper_abs_PhiR_mul_sq_le
-- name    : Zeta23.Taper.abs_PhiR_mul_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:58.960604+00:00
-- url     : https://prove2.me/theorems/c9478adb-70fe-447b-b75d-847199a47675
-- title:
--   Second-order decay: $|\Phi(r)|\, r^2 \le c_\varrho / w$
-- statement:
--   **Setup.** Let $\varrho$ be a taper profile and $\varphi(u) = \varrho\bigl((L/2-|u|)/w\bigr)$ the taper, now with $1 \le w$ and $2w \le L$. As before, `PhiR ϱ L w r` $= \operatorname{Re}\Phi(r)$ where $\Phi = \widehat{\varphi^2}$ is the paper Fourier transform of $\varphi^2$. The profile constant of [eq:phinorms] is
--   $$c_\varrho \;:=\; 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$$
--   (`cRho ϱ`, with $\|\varrho'\|_\infty = \sup_x |\varrho'(x)|$ and $\|\varrho''\|_1 = \int |\varrho''|$), depending only on $\varrho$.
--
--   **Statement.** For every real $r$,
--   $$|\Phi(r)|\cdot r^{2} \;\le\; \frac{c_\varrho}{w}.$$
--   This is the two-integrations-by-parts decay $|\Phi(r)|\,r^2 \le \int |(\varphi^2)''|$, with the second-derivative mass of $\varphi^2$ bounded by $c_\varrho/w$ (the ramps have width $w$, so derivatives of $\varphi$ scale like $1/w$).
--
--   **Role.** The strongest of the three bounds forming the envelope $\psi$ of [eq:psidef]: it makes $\Phi$ integrable on $\mathbb{R}$ with controlled tail mass. Consumed by `Zeta23.PrimeSide.localHyps_concrete` and `Zeta23.Taper.integral_PhiR_sq_mul_sq_le` in the mollified second-moment (prime-side) part of the proof.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L353-L363

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

theorem Zeta23.Taper.abs_PhiR_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| * r ^ 2 ≤ cRho ϱ / w := by sorry
