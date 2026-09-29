-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_psi_Ioi_le
-- name    : Zeta23.Taper.integral_psi_Ioi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:30.695172+00:00
-- url     : https://prove2.me/theorems/f83ff289-4958-431c-a04f-3b40dc7fba7f
-- title:
--   First $\psi$-integral of [eq:psiints]: $\int_0^\infty \psi \le 4 + 2\log\!\big(c_\varrho L/(4w)\big)$
-- statement:
--   Fix a taper profile $\varrho$, support length $L$ and ramp width $w$, and let $\psi$ be the decay majorant of [eq:psidef]: $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ for $r \ne 0$ and $\psi(0) := L$ (the value at $0$ is made explicit because Lean's convention $2/0 = 0$ would otherwise misread the paper's $\min(L, \infty, \infty)$). Here $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$.
--
--   Assuming $1 \le w$ and $8w \le L$, the theorem asserts the bound of [eq:psiints] on the one-sided mass $\Psi_0$:
--   $$\int_0^{\infty} \psi(r)\,dr \;\le\; 4 + 2\log\!\left(\frac{c_\varrho L}{4w}\right).$$
--   The paper states this with an asymptotic "$=$"; the formalization proves the inequality, which is all that is used downstream.
--
--   In the project this integral is one of the quantitative inputs to `Zeta23.PrimeSide.localHyps_concrete`, the node that instantiates the local hypotheses of the prime-side estimates with the concrete taper family.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L620-L673, docstring tag [eq:psiints]

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

theorem Zeta23.Taper.integral_psi_Ioi_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r in Ioi 0, psi ϱ L w r ≤ 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by sorry
