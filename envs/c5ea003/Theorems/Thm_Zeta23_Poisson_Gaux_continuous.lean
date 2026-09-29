-- Prove2me | Theorems.Thm_Zeta23_Poisson_Gaux_continuous
-- name    : Zeta23.Poisson.Gaux_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:58:01.5617+00:00
-- url     : https://prove2.me/theorems/116eb613-6a36-448f-99be-3a37df6819b3
-- title:
--   Continuity of the auxiliary function $G$ in the Poisson-summation argument
-- statement:
--   Fix real parameters $L, T, \tau, \tau'$ and a window $\varphi \colon \mathbb{R} \to \mathbb{R}$. The auxiliary function of the Poisson-summation argument is
--   $$G(\xi) \;=\; L \int_{\mathbb{R}} \varphi(u)\, \varphi(L\xi - u)\, e^{\,i\,(\tau u + \tau'(L\xi - u) - T L \xi)}\, du,$$
--   formalized as `Gaux φ L T τ τ'` (the integral of the kernel `gInt`). The theorem asserts: if $L > 0$, $\varphi$ is continuous, and $\varphi(u) = 0$ whenever $|u| \ge L/2$ (compact support in $[-L/2, L/2]$), then $G$ is continuous on $\mathbb{R}$.
--
--   Continuity of $G$ (together with its compact support and the decay of its Fourier transform) is one of the hypotheses of Mathlib's Poisson summation formula; the consumer is `Zeta23.Poisson.hasSum_paperFT_mul_paperFT`, the core Gabor-system identity [lem:poisson] in the module `Zeta23.Poisson`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean#L137-L151

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Poisson
variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)
variable {φ L T τ τ'}

theorem Zeta23.Poisson.Gaux_continuous (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) : Continuous (Gaux φ L T τ τ') := by sorry
