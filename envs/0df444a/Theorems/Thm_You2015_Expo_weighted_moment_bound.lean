-- Prove2me | Theorems.Thm_You2015_Expo_weighted_moment_bound
-- name    : You2015.Expo.weighted_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:13:42.040098+00:00
-- url     : https://prove2.me/theorems/46f8bd6a-5eb5-4fbb-89c9-efb33faa8221
-- title:
--   Eq. (4.14) — c₁e^{γt}𝔼|x(t)|² ≤ C for all t ≥ 2τ, for γ > 0 solving (4.4)
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma=(\gamma_{ij})$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (constants $K_1,K_2>0$) and Assumption 2.2 (constant $K_3>0$). Let $U\in C^{2,1}(\mathbb R^n\times S\times\mathbb R_+;\mathbb R_+)$ and $\lambda_1,\lambda_2>0$ satisfy Assumption 3.1, and let the observation interval $\tau>0$ satisfy (3.5):
--   $$\lambda_2>\frac{\tau K_3^2}{\lambda_1}\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\quad\text{and}\quad\tau\le\frac1{4K_3}.$$
--   Let moreover $U$ satisfy Assumption 4.1 with constants $c_1,c_2>0$: $c_1|x|^2\le U(x,i,t)\le c_2|x|^2$.
--   Fix initial data $x_0\in\mathbb R^n$ and $r_0\in S$, a stochastic basis (a filtration under the usual conditions, an $m$-dimensional Brownian motion $w$ and a Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1), $dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t)$, $x(0)=x_0$, with $\delta_t=[t/\tau]\tau$.
--   Write
--   $$\theta=\frac{K_3^2}{\lambda_1},\qquad\lambda=\lambda_2-\theta\tau\big[2\tau(K_1^2+2K_3^2)+K_2^2\big],$$
--   $$H_1=\theta\tau\big(2\tau(K_1^2+2K_3^2)+K_2^2\big)+\frac{24\,\theta\tau^4K_3^4}{1-6\tau^2K_3^2},\qquad H_2=\frac{12\theta\tau^2K_3^2(\tau K_1^2+K_2^2)}{1-6\tau^2K_3^2}.$$
--   Let $\gamma>0$ satisfy
--   $$2\tau\gamma e^{2\tau\gamma}(H_1+\tau H_2)+\gamma c_2=\lambda.\tag{4.4}$$
--   Then there is a constant $C$ (depending on the data, on $x_0$, $r_0$, the solution and $\gamma$, but not on $t$) such that
--   $$c_1e^{\gamma t}\,\mathbb E|x(t)|^2\le C\qquad\text{for all }t\ge2\tau.\tag{4.14}$$
--
--   This is the exponential moment bound from which the mean-square part (4.2) of Theorem 4.2 follows immediately, and from which the almost-sure part (4.3) follows by a general mean-square-to-almost-sure transfer.
--
--   **Formalization Note** The constant $H_1$ is the one the paper's proof of Theorem 4.2 actually uses: combining (4.9) with (3.21), the coefficient of $\int\mathbb E|x(v)|^2dv$ is $\theta\tau(2\tau(K_1^2+2K_3^2)+K_2^2)+\theta\tau\cdot4\tau K_3^2\cdot\frac{6\tau^2K_3^2}{1-6\tau^2K_3^2}$. The page prints $24\tau^3K_3^4$ in place of $24\theta\tau^4K_3^4$ in (4.5), dropping the factor $\theta\tau$; this statement uses the corrected value. The constant $C$ is quantified after $x_0,r_0$, the solution and $\gamma$ and before $t$. The inequality is stated in $[0,\infty]$ with the left factor and $C$ embedded as nonnegative reals, so it also asserts $\mathbb E|x(t)|^2<\infty$. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 919, Eq. (4.14) (in the proof of Theorem 4.2), with (4.4)–(4.5); H₁ corrected

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Expo_Assumptions
import Definitions.Def_You2015_Expo_Constants

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Expo

theorem weighted_moment_bound
    {n m N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) (hΓ : You2015.Shared.IsGenerator Γ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ K₃ : ℝ) (h21 : Assumption21 f g K₁ K₂) (h22 : Assumption22 u K₃)
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (hU : C21 U Ut Ux Uxx) (lam₁ lam₂ : ℝ) (h31 : Assumption31 Γ f u g U Ut Ux Uxx lam₁ lam₂)
    (c₁ c₂ : ℝ) (h41 : Assumption41 U c₁ c₂)
    (τ : ℝ≥0) (h35 : Condition35 K₁ K₂ K₃ lam₁ lam₂ τ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r₀ : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : You2015.Shared.HybridSetup P m N Γ r₀) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hx : You2015.Shared.SolvesSampledHybridSDE S f u g τ x₀ x) :
    ∀ γ : ℝ, 0 < γ → rateEquationLHS K₁ K₂ K₃ lam₁ c₂ τ γ = lam K₁ K₂ K₃ lam₁ lam₂ τ →
      ∃ C : ℝ, ∀ t : ℝ≥0, 2 * τ ≤ t →
        ENNReal.ofReal (c₁ * Real.exp (γ * t)) * ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C := by sorry

end You2015.Expo
