-- Prove2me | Theorems.Thm_Zeta23_Poisson_hasSum_paperFT_mul_paperFT
-- name    : Zeta23.Poisson.hasSum_paperFT_mul_paperFT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:58:45.419403+00:00
-- url     : https://prove2.me/theorems/9cf571c3-cc11-4b59-ac5c-a93699ed1aba
-- title:
--   Poisson summation for the Gabor system: $\sum_{k\in\mathbb{Z}} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k) = L\,\widehat{\varphi^2}(\tau-\tau')$
-- statement:
--   Let $\varphi \colon \mathbb{R} \to \mathbb{R}$ be an abstract window and $L > 0$, with: $\varphi$ continuous; $\varphi(u) = 0$ whenever $|u| \ge L/2$ (support in $[-L/2, L/2]$); $\varphi$ even; and the decay hypothesis that $|\hat\varphi(s)|\,(1 + s^2)$ is bounded on $\mathbb{R}$, where $\hat\varphi(s) = \int \varphi(u)\, e^{isu}\, du$ is the paper's Fourier convention (`Zeta23.paperFT`).
--
--   Then for all real $T, \tau, \tau'$, with grid points $\tau_k := T + k \cdot \frac{2\pi}{L}$ ($k \in \mathbb{Z}$),
--   $$\sum_{k \in \mathbb{Z}} \hat\varphi(\tau - \tau_k)\; \hat\varphi(\tau' - \tau_k) \;=\; L \cdot \widehat{\varphi^2}(\tau - \tau'),$$
--   where $\widehat{\varphi^2}$ is the paper transform of $u \mapsto \varphi(u)^2$ (the paper's $\Phi$, [eq:PhigA]). The statement is a `HasSum` over $k \in \mathbb{Z}$: the family is summable with the stated value. This is the core identity [lem:poisson] ("Poisson summation for the Gabor system") in complex form and for real arguments $\tau, \tau'$ — all that [prop:block](ii) uses.
--
--   The proof applies Mathlib's Poisson summation to the auxiliary function $G$: $G$ is continuous with support in $[-1,1]$, $G(k) = 0$ for $k \in \mathbb{Z}\setminus\{0\}$ while $G(0) = L\,\widehat{\varphi^2}(\tau-\tau')$, and $\mathcal{F}G(w) = \hat\varphi(\tau - \tau_w)\hat\varphi(\tau' - \tau_w)$. Its consumer is `Zeta23.Taper.hasSum_phiHatR_mul`, which specializes it to the project's concrete taper and hands the kernel identity $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ to the block-diagonalization of the zero-side matrix.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean#L259-L326, docstring tag [lem:poisson]

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

theorem Zeta23.Poisson.hasSum_paperFT_mul_paperFT {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (heven : ∀ u, φ (-u) = φ u)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
                        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      (L * paperFT (fun u => ((φ u ^ 2 : ℝ) : ℂ)) ((τ - τ' : ℝ) : ℂ)) := by sorry
