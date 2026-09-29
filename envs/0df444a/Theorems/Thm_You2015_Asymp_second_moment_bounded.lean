-- Prove2me | Theorems.Thm_You2015_Asymp_second_moment_bounded
-- name    : You2015.Asymp.second_moment_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:34:55.189844+00:00
-- url     : https://prove2.me/theorems/7b9592dc-0b83-45f9-9cd4-28135e524a2a
-- title:
--   Eq. (3.23) — the second moment 𝔼|x(t)|² is bounded uniformly in t ≥ 0
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma=(\gamma_{ij})$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (with constants $K_1,K_2>0$) and Assumption 2.2 (with constant $K_3>0$). Let $U\in C^{2,1}(\mathbb R^n\times S\times\mathbb R_+;\mathbb R_+)$ and $\lambda_1,\lambda_2>0$ satisfy Assumption 3.1, and let the observation interval $\tau>0$ satisfy (3.5):
--   $$\lambda_2>\frac{\tau K_3^2}{\lambda_1}\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\quad\text{and}\quad\tau\le\frac1{4K_3}.$$
--   Fix initial data $x_0\in\mathbb R^n$ and $r_0\in S$, a stochastic basis (a filtration under the usual conditions, an $m$-dimensional Brownian motion $w$ and a Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1), $dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t)$, $x(0)=x_0$, with $\delta_t=[t/\tau]\tau$.
--
--   Then there is a positive constant $C$ such that
--   $$\mathbb E|x(t)|^2\le C\qquad\forall t\ge0.\tag{3.23}$$
--
--   The bound is uniform in time; together with the Lipschitz continuity of $t\mapsto\mathbb E|x(t)|^2$ it is what turns the integrability (3.6) into the convergence of Theorem 3.3.
--
--   **Formalization Note** The paper's "$C$ denotes a positive constant that may change from line to line" (p. 912) is read as an existential constant chosen after the data, the initial data and the solution, and before $t$: $C$ may depend on $x_0$, $r_0$ and the solution, but not on $t$. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 913, Eq. (3.23) (in the proof of Theorem 3.3)

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Asymp_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Asymp

theorem second_moment_bounded
    {n m N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) (hΓ : You2015.Shared.IsGenerator Γ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ K₃ : ℝ) (h21 : Assumption21 f g K₁ K₂) (h22 : Assumption22 u K₃)
    (U Ut : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → ℝ)
    (Ux : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (Uxx : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (hU : C21 U Ut Ux Uxx) (lam₁ lam₂ : ℝ) (h31 : Assumption31 Γ f u g U Ut Ux Uxx lam₁ lam₂)
    (τ : ℝ≥0) (h35 : Condition35 K₁ K₂ K₃ lam₁ lam₂ τ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r₀ : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : You2015.Shared.HybridSetup P m N Γ r₀) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hx : You2015.Shared.SolvesSampledHybridSDE S f u g τ x₀ x) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ≥0, ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C := by sorry

end You2015.Asymp
