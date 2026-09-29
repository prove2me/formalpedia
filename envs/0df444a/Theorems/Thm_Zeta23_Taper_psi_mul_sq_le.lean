-- Prove2me | Theorems.Thm_Zeta23_Taper_psi_mul_sq_le
-- name    : Zeta23.Taper.psi_mul_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:07.036298+00:00
-- url     : https://prove2.me/theorems/4e97ad8f-4282-4ca5-8611-942379da8c3c
-- title:
--   Quadratic-weight bound for $\psi$: $\psi(r)\,r^2 \le c_\varrho/w$
-- statement:
--   Let $\varrho$ be a taper profile with constant $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$, and let $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ (with $\psi(0) := L$) be the decay majorant of [eq:psidef].
--
--   Assuming $1 \le w$ (and $2w \le L$, present in the statement but not used in the proof), the theorem asserts, for every real $r$,
--   $$\psi(r)\, r^2 \;\le\; \frac{c_\varrho}{w}.$$
--   For $r \ne 0$ this is immediate from the third entry of the minimum, $\psi(r) \le c_\varrho/(w r^2)$; at $r = 0$ the left side vanishes and the right side is nonnegative (indeed $c_\varrho \ge 4$).
--
--   In the project this pointwise bound drives the tail estimates for the $\psi$-integrals: it feeds `integral_psi_Ioi_le`, `integral_psi_sq_mul_abs_le`, the integrability lemmas `psi_sq_integrable` and `psi_sq_mul_abs_integrable`, and `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L417-L426

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

theorem Zeta23.Taper.psi_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r * r ^ 2 ≤ cRho ϱ / w := by sorry
