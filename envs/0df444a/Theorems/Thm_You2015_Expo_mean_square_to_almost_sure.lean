-- Prove2me | Theorems.Thm_You2015_Expo_mean_square_to_almost_sure
-- name    : You2015.Expo.mean_square_to_almost_sure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:14:24.174684+00:00
-- url     : https://prove2.me/theorems/dfd6c709-1371-4b57-b134-e3bda6cff791
-- title:
--   End of the proof of Theorem 4.2 — (4.14) implies (4.3): mean-square exponential decay gives almost sure exponential decay (Mao–Yuan [23, Thm 8.8])
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (constants $K_1,K_2>0$) and Assumption 2.2 (constant $K_3>0$), and let $\tau>0$. Fix initial data $x_0\in\mathbb R^n$ and $r_0\in S$, a stochastic basis (a filtration under the usual conditions, an $m$-dimensional Brownian motion $w$ and a Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1), $dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t)$, $x(0)=x_0$, with $\delta_t=[t/\tau]\tau$.
--
--   Let $\gamma>0$ and suppose there is a constant $C$ with
--   $$e^{\gamma t}\,\mathbb E|x(t)|^2\le C\qquad\text{for all }t\ge2\tau.$$
--   Then
--   $$\limsup_{t\to\infty}\frac1t\log|x(t)|\le-\frac\gamma2\quad\text{a.s.},$$
--   that is, almost surely, for every $\gamma'<\gamma$, $|x(t)|\le e^{-\gamma' t/2}$ for all sufficiently large $t$.
--
--   The paper obtains (4.3) from (4.14) in the last sentence of the proof of Theorem 4.2 by citing Mao–Yuan [23, Theorem 8.8 on page 309]: for a stochastic delay equation whose coefficients grow at most linearly, mean-square exponential stability implies almost sure exponential stability. The paper does not prove this step.
--
--   **Formalization Note** The step needs only the linear growth of the coefficients (Assumptions 2.1, 2.2) and the bounded delay $t-\delta_t\le\tau$, not Assumptions 3.1 or 4.1, so it is stated under Assumptions 2.1, 2.2 and $\tau>0$; the constant $c_1>0$ of (4.14) is absorbed into $C$. With $\log0=-\infty$, $\limsup_{t\to\infty}\frac1t\log a(t)\le-\gamma/2$ for $a(t)\ge0$ is equivalent to: for every $\gamma'<\gamma$, eventually $a(t)\le e^{-\gamma't/2}$; the statement uses this form, so no value of Lean's `Real.log` at $0$ enters. The almost-sure quantifier is outside the quantifier over $\gamma'$, as in the paper. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 919, last sentence of the proof of Theorem 4.2 ((4.14) ⇒ (4.3), citing Mao–Yuan [23, Theorem 8.8, p. 309])

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Expo_Assumptions
import Definitions.Def_You2015_Expo_Constants

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Expo

theorem mean_square_to_almost_sure
    {n m N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) (hΓ : You2015.Shared.IsGenerator Γ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ K₃ : ℝ) (h21 : Assumption21 f g K₁ K₂) (h22 : Assumption22 u K₃)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r₀ : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : You2015.Shared.HybridSetup P m N Γ r₀) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hx : You2015.Shared.SolvesSampledHybridSDE S f u g τ x₀ x) :
    ∀ γ : ℝ, 0 < γ →
      (∃ C : ℝ, ∀ t : ℝ≥0, 2 * τ ≤ t →
        ENNReal.ofReal (Real.exp (γ * t)) * ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C) →
      ∀ᵐ ω ∂P, ∀ γ' : ℝ, γ' < γ →
        ∀ᶠ t : ℝ≥0 in atTop, ‖x t ω‖ ≤ Real.exp (-(γ' * t / 2)) := by sorry

end You2015.Expo
