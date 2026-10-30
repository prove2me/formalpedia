-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_quasiPowers_tendstoInDistribution_of_continuousAt
-- name    : AnalyticCombinatorics.Ch9.LimitLaws.quasiPowers_tendstoInDistribution_of_continuousAt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T10:33:04.964793+00:00
-- url     : https://prove2.me/theorems/6945e538-63a4-4dae-97eb-3e7c949de78d
-- title:
--   Conditional quasi-powers Gaussian criterion
-- statement:
--   For each natural $n$, let $(\Omega_n,\mathcal F_n,P_n)$ be a probability space and let $X_n:\Omega_n\to\mathbb R$ be almost-everywhere measurable. The spaces and measures may depend on $n$; no coupling or independence between different $n$ is assumed. Let real $\beta_n\to+\infty$, let $u_1,u_2\in\mathbb R$ with $u_2>0$, and let $R_n:\mathbb C\to\mathbb C$ and $V:\mathbb C\to\mathbb C$ satisfy continuity of $V$ at $0$ and $V(0)=0$.
--
--   Write $\phi_n(s)=\int_{\Omega_n}e^{isX_n}\,dP_n$. Assume a single real $s_0>0$ works for every natural $n$ and every real $|s|\le s_0$ in
--
--   $$\phi_n(s)=\exp\!\left(\beta_n\left[u_1is+\frac{u_2(is)^2}{2}+R_n(is)\right]+V(is)\right).$$
--
--   For each fixed real $t$, put $z_n(t)=i(\sqrt{\beta_nu_2})^{-1}t$ and assume
--
--   $$\beta_nR_n(z_n(t))\longrightarrow0\quad\text{in }\mathbb C.$$
--
--   Then the laws under the respective $P_n$ of
--
--   $$Y_n=\frac{X_n-\beta_nu_1}{\sqrt{\beta_nu_2}}$$
--
--   converge weakly to the law of the identity random variable on $\mathbb R$ under the mean-zero, variance-one Gaussian measure. The limit probability space is separate from the $\Omega_n$. The expansion and scaled-remainder limit are genuine premises; no holomorphy, uniform-in-$t$ error bound, rate or exact expectation/variance identity is asserted. Early nonpositive $\beta_n$ use the source's totalized square root/division conventions and do not affect the eventual limit.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/QuasiPowers.lean#L300. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_QuasiPowers
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Quasi-powers and Gaussian limit laws

This file formalizes the Mathlib-supported core of Hwang's quasi-powers theorem.

Mathlib v4.29.0 has Levy's continuity theorem for characteristic functions as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, but not a
corresponding Curtiss-style continuity theorem for moment-generating functions.
Accordingly the main limit theorem below takes a logarithmic quasi-powers expansion
on the imaginary axis, proves convergence of normalized characteristic functions,
and then applies Levy's theorem.
-/

open Asymptotics Complex Filter MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Topology

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch9
open AnalyticCombinatorics.Ch9.LimitLaws

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β ε₁ ε₂ : ℕ → ℝ} {u₁ u₂ : ℝ}

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)}
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β : ℕ → ℝ} {u₁ u₂ : ℝ} {R : ℕ → ℂ → ℂ} {V : ℂ → ℂ}

variable [∀ n, IsProbabilityMeasure (P n)]

theorem AnalyticCombinatorics.Ch9.LimitLaws.quasiPowers_tendstoInDistribution_of_continuousAt
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hVcont : ContinuousAt V 0) (hV0 : V 0 = 0)
    (hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0)) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) := by sorry
