-- Prove2me | Theorems.Thm_Zeta23_Taper_psi_measurable
-- name    : Zeta23.Taper.psi_measurable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:36:26.737559+00:00
-- url     : https://prove2.me/theorems/89d9f2b6-d5f7-40ef-ad02-8df43365309e
-- title:
--   Measurability of the decay majorant $\psi$
-- statement:
--   Let $\psi$ be the decay majorant of [eq:psidef] attached to a profile $\varrho$, support length $L$ and ramp width $w$: $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ for $r \ne 0$, and $\psi(0) := L$, where $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$.
--
--   The theorem asserts that $\psi$ is a (Borel) measurable function $\mathbb{R} \to \mathbb{R}$. No hypotheses are needed: the statement holds for arbitrary $\varrho$, $L$, $w$, since $\psi$ is a piecewise combination (over the singleton $\{0\}$ and its complement) of measurable expressions in $r$.
--
--   In the project this measurability underlies the integrability lemmas `psi_sq_integrable` and `psi_sq_mul_abs_integrable`, and enters `Zeta23.PrimeSide.localHyps_concrete` directly.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L434-L445

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

theorem Zeta23.Taper.psi_measurable : Measurable (psi ϱ L w) := by sorry
