-- Prove2me | Theorems.Thm_You2015_Expo_exponential_stability
-- name    : You2015.Expo.exponential_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:15:02.946934+00:00
-- url     : https://prove2.me/theorems/03273b96-ca92-4568-9a85-588780b3f410
-- title:
--   Theorem 4.2 — mean-square and almost sure exponential stability of the discrete-observation feedback system (2.1), with rate γ the unique root of (4.4)
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma=(\gamma_{ij})$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (constants $K_1,K_2>0$) and Assumption 2.2 (constant $K_3>0$). Let $U\in C^{2,1}(\mathbb R^n\times S\times\mathbb R_+;\mathbb R_+)$ and $\lambda_1,\lambda_2>0$ satisfy Assumption 3.1, and let the observation interval $\tau>0$ satisfy (3.5):
--   $$\lambda_2>\frac{\tau K_3^2}{\lambda_1}\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\quad\text{and}\quad\tau\le\frac1{4K_3}.$$
--   Let moreover $U$ satisfy Assumption 4.1 with constants $c_1,c_2>0$: $c_1|x|^2\le U(x,i,t)\le c_2|x|^2$.
--   Fix initial data $x_0\in\mathbb R^n$ and $r_0\in S$, a stochastic basis (a filtration under the usual conditions, an $m$-dimensional Brownian motion $w$ and a Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1), $dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t)$, $x(0)=x_0$, with $\delta_t=[t/\tau]\tau$.
--   Write
--   $$\theta=\frac{K_3^2}{\lambda_1},\qquad\lambda=\lambda_2-\theta\tau\big[2\tau(K_1^2+2K_3^2)+K_2^2\big],$$
--   $$H_1=\theta\tau\big(2\tau(K_1^2+2K_3^2)+K_2^2\big)+\frac{24\,\theta\tau^4K_3^4}{1-6\tau^2K_3^2},\qquad H_2=\frac{12\theta\tau^2K_3^2(\tau K_1^2+K_2^2)}{1-6\tau^2K_3^2}.$$
--   Then:
--
--   1. the equation
--   $$2\tau\gamma e^{2\tau\gamma}(H_1+\tau H_2)+\gamma c_2=\lambda\tag{4.4}$$
--   has exactly one root $\gamma>0$; and
--   2. for this $\gamma$ the solution satisfies
--   $$\limsup_{t\to\infty}\frac1t\log\big(\mathbb E|x(t)|^2\big)\le-\gamma\tag{4.2}$$
--   and
--   $$\limsup_{t\to\infty}\frac1t\log|x(t)|\le-\frac\gamma2\quad\text{a.s.}\tag{4.3}$$
--
--   This is the paper's second main result: a feedback control that observes the state only at the times $0,\tau,2\tau,\dots$ makes the hybrid system exponentially stable, both in mean square and almost surely, with an explicit rate, provided $\tau$ is small enough for (3.5) and the Lyapunov function has quadratic bounds.
--
--   **Formalization Note** The constant $H_1$ is the one the paper's proof of Theorem 4.2 actually uses: combining (4.9) with (3.21), the coefficient of $\int\mathbb E|x(v)|^2dv$ is $\theta\tau(2\tau(K_1^2+2K_3^2)+K_2^2)+\theta\tau\cdot4\tau K_3^2\cdot\frac{6\tau^2K_3^2}{1-6\tau^2K_3^2}$. The page prints $24\tau^3K_3^4$ in place of $24\theta\tau^4K_3^4$ in (4.5), dropping the factor $\theta\tau$; this statement uses the corrected value. Under the printed $H_1$ the claimed rate could exceed what the proof establishes whenever $\theta\tau>1$. "Let $\tau>0$ be sufficiently small for (3.5)" is read as "for every $\tau>0$ satisfying (3.5)"; $U,\lambda_1,\lambda_2,c_1,c_2,\tau$ are data. "(so $\lambda>0$)" is a consequence of (3.5) and is not assumed. "$\gamma>0$ is the unique root" is stated as conjunct 1; conjunct 2 is stated for every positive root, which by conjunct 1 is that root. The paper's logarithms take the value $-\infty$ at $0$ (for $x_0=0$ the solution is $0$); with that convention, for a finite $a(t)\ge0$, $\limsup_{t\to\infty}\frac1t\log a(t)\le-\gamma$ is equivalent to: for every $\gamma'<\gamma$, eventually $a(t)\le e^{-\gamma't}$. (4.2) and (4.3) are stated in this form, so Lean's `Real.log 0 = 0` never enters. In (4.3) the almost-sure quantifier is outside the quantifier over $\gamma'$, as in the paper. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, pp. 917–918, Theorem 4.2 (Eqs. (4.2)–(4.5); H₁ of (4.5) corrected, see the statement)

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Expo_Assumptions
import Definitions.Def_You2015_Expo_Constants

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Expo

theorem exponential_stability
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
    (∃! γ : ℝ, 0 < γ ∧
        rateEquationLHS K₁ K₂ K₃ lam₁ c₂ τ γ = lam K₁ K₂ K₃ lam₁ lam₂ τ) ∧
    ∀ γ : ℝ, 0 < γ → rateEquationLHS K₁ K₂ K₃ lam₁ c₂ τ γ = lam K₁ K₂ K₃ lam₁ lam₂ τ →
      (∀ γ' : ℝ, γ' < γ → ∀ᶠ t : ℝ≥0 in atTop,
          ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (Real.exp (-(γ' * t)))) ∧
      (∀ᵐ ω ∂P, ∀ γ' : ℝ, γ' < γ →
          ∀ᶠ t : ℝ≥0 in atTop, ‖x t ω‖ ≤ Real.exp (-(γ' * t / 2))) := by sorry

end You2015.Expo
