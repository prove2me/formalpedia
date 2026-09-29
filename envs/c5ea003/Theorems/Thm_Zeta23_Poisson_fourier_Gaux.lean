-- Prove2me | Theorems.Thm_Zeta23_Poisson_fourier_Gaux
-- name    : Zeta23.Poisson.fourier_Gaux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:58:16.588306+00:00
-- url     : https://prove2.me/theorems/5db1943a-8ff3-4283-b14b-87e6f86caa71
-- title:
--   Fourier transform of $G$: $\mathcal{F}G(w) = \hat\varphi(\tau - \tau_w)\,\hat\varphi(\tau' - \tau_w)$
-- statement:
--   Fix real parameters $L, T, \tau, \tau'$ and a window $\varphi \colon \mathbb{R} \to \mathbb{R}$, and let $G$ be the auxiliary function
--   $$G(\xi) \;=\; L \int_{\mathbb{R}} \varphi(u)\, \varphi(L\xi - u)\, e^{\,i\,(\tau u + \tau'(L\xi - u) - T L \xi)}\, du.$$
--   Write $\hat\varphi(s) = \int \varphi(u)\, e^{isu}\, du$ for the paper's Fourier convention (`Zeta23.paperFT`), and $\mathcal{F}$ for Mathlib's Fourier transform, $\mathcal{F}f(w) = \int f(\xi)\, e^{-2\pi i w \xi}\, d\xi$. The theorem asserts: if $L > 0$, $\varphi$ is continuous, and $\varphi(u) = 0$ for $|u| \ge L/2$, then for every real $w$,
--   $$\mathcal{F}G(w) \;=\; \hat\varphi(\tau - \tau_w)\; \hat\varphi(\tau' - \tau_w), \qquad \tau_w \;:=\; T + w \cdot \frac{2\pi}{L}.$$
--   The proof is a Fubini computation on the compactly supported two-variable integrand.
--
--   This identifies the Fourier coefficients appearing on the dual side of Poisson summation; the consumer is `Zeta23.Poisson.hasSum_paperFT_mul_paperFT`, the core identity [lem:poisson] of the module `Zeta23.Poisson`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean#L188-L255

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

theorem Zeta23.Poisson.fourier_Gaux (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (w : ℝ) :
    𝓕 (Gaux φ L T τ τ') w
      = paperFT (fun u => (φ u : ℂ)) ((τ - (T + w * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + w * (2 * π / L)) : ℝ) : ℂ) := by sorry
