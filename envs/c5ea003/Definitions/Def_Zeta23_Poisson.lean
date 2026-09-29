-- Prove2me | Definitions.Def_Zeta23_Poisson
-- name    : Zeta23_Poisson
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:09:30.357363+00:00
-- url     : https://prove2.me/theorems/2680600e-0d2f-462b-9248-e212cc75f6ea
-- title:
--   The auxiliary function $G$ for Poisson summation of the Gabor system
-- statement:
--   This bundle defines the auxiliary function through which the project proves [lem:poisson], the Poisson-summation identity for the Gabor system of the paper (§2.2):
--   $$K_\infty(\tau,\tau') := \sum_{k \in \mathbb{Z}} \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau' - \tau_k) \;=\; L\, \Phi(\tau - \tau'),$$
--   where $\tau_k := T + kh$, $h := 2\pi/L$, $\Phi := \widehat{\varphi^2}$, and $\hat\varphi(s) = \int \varphi(u) e^{isu}\,du$ is the paper's Fourier convention.
--
--   Given the taper $\varphi : \mathbb{R} \to \mathbb{R}$ and reals $L, T, \tau, \tau'$, the members are: `Poisson.gInt`, the integrand $(\xi, u) \mapsto L\, \varphi(u)\, \varphi(L\xi - u)\, e^{i(\tau u + \tau'(L\xi - u) - TL\xi)}$; and `Poisson.Gaux`, the function
--   $$G(\xi) \;:=\; L \int_{\mathbb{R}} \varphi(u)\, \varphi(L\xi - u)\, e^{i(\tau u + \tau'(L\xi - u) - TL\xi)}\, du,$$
--   i.e. $G(\xi) = L\, e^{-iTL\xi} (\varphi_\tau * \varphi_{\tau'})(L\xi)$.
--
--   Role: $G$ is continuous with support in $[-1,1]$, satisfies $G(k) = 0$ for integer $k \neq 0$ and $G(0) = L\,\Phi(\tau - \tau')$, and its Fourier transform is $\mathcal{F}G(w) = \hat\varphi(\tau - \tau_w)\hat\varphi(\tau' - \tau_w)$; applying Mathlib's Poisson summation to $G$ yields [lem:poisson], the key kernel identity behind the prime-side trace computations ([eq:Kdef], [lem:ends]).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean, docstring tag [lem:poisson]

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
import Definitions.Def_Zeta23_Taper_Basic

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
[lem:poisson] "Poisson summation for the Gabor system", the paper §2.2:

  "For all τ, τ' ∈ ℝ,
     K_∞(τ,τ') := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L·Φ(τ−τ'),   in particular   Σ_{k∈ℤ} φ̂(τ−τ_k)² = aL²."

Here τ_k := T + k h, h := 2π/L [eq:fk], Φ := (φ²)^ [eq:PhigA], a := L⁻¹∫φ² [eq:abdef], and
φ̂(s) = ∫ φ(u) e^{isu} du is the paper's Fourier convention (`Zeta23.paperFT`).  Only the
real-argument identity is proved (that is all [prop:block](ii) uses; the complex continuation
mentioned in [rem:pairblock] is not used by the proof).

Proof route (the paper's, rearranged so that Fourier inversion is not needed): with
  G(ξ) := L · ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du      (= L e^{−iTLξ}(φ_τ ∗ φ_{τ'})(Lξ)),
G is continuous with support in [−1,1] and G(k) = 0 for k ∈ ℤ∖{0} (because φ(u) = 0 for
|u| ≥ L/2), G(0) = L ∫ φ(u)φ(−u)e^{i(τ−τ')u} du = L Φ(τ−τ') (φ even), and a Fubini computation
gives 𝓕G(w) = φ̂(τ−τ_w) φ̂(τ'−τ_w) for Mathlib's 𝓕 and every real w (τ_w := T + w·2π/L).
Mathlib's Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
(Σ_k G(k) = Σ_n 𝓕G(n)) then gives the claim; summability of n ↦ φ̂(τ−τ_n)φ̂(τ'−τ_n) comes from
the decay |φ̂(r)| ≪ (1+r²)⁻¹, i.e. [eq:hfbound]/[eq:psidef].
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23

namespace Poisson

/-! #### A decay-to-`IsBigO` lemma -/


/-! #### The auxiliary function `G` -/

variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)

/-- Integrand of `G`: `(ξ,u) ↦ L φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)}`. -/
noncomputable def gInt (ξ u : ℝ) : ℂ :=
  (L : ℂ) * ((φ u : ℂ) * (φ (L * ξ - u) : ℂ) *
    cexp (I * (τ * u + τ' * (L * ξ - u) - T * L * ξ)))

/-- `G(ξ) := L ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du` (see module docstring). -/
noncomputable def Gaux (ξ : ℝ) : ℂ := ∫ u, gInt φ L T τ τ' ξ u

variable {φ L T τ τ'}










/-! #### The abstract identity -/


end Poisson

namespace Taper

variable {ϱ : ℝ → ℝ} {L w : ℝ}




end Taper

namespace Params

variable {P : Params} {T : ℝ}


variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL




end Params

end Zeta23


