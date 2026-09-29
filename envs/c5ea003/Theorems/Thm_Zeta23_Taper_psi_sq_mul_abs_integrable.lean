-- Prove2me | Theorems.Thm_Zeta23_Taper_psi_sq_mul_abs_integrable
-- name    : Zeta23.Taper.psi_sq_mul_abs_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:36:32.477277+00:00
-- url     : https://prove2.me/theorems/f4792dec-adbd-49e4-b581-c52177e03c87
-- title:
--   Integrability of $\psi(r)^2|r|$ on $\mathbb{R}$
-- statement:
--   Let $\varrho$ be a taper profile with constant $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$, and let $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ (with $\psi(0) := L$) be the decay majorant of [eq:psidef].
--
--   Assuming $1 \le w$ and $8w \le L$, the theorem asserts that the function
--   $$r \;\longmapsto\; \psi(r)^2\,|r|$$
--   is integrable on $\mathbb{R}$: near the origin it is bounded (by $L^2|r|$), and at infinity it decays like $|r|^{-3}$ thanks to $\psi(r) \le c_\varrho/(w r^2)$.
--
--   In the project this integrability certificate accompanies the quantitative moment bound `integral_psi_sq_mul_abs_le` and is consumed by `Zeta23.PrimeSide.localHyps_concrete`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L865-L874

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

theorem Zeta23.Taper.psi_sq_mul_abs_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => psi ϱ L w r ^ 2 * |r|) := by sorry
