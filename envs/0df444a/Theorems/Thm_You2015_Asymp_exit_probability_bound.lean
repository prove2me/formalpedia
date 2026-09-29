-- Prove2me | Theorems.Thm_You2015_Asymp_exit_probability_bound
-- name    : You2015.Asymp.exit_probability_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:37:35.837443+00:00
-- url     : https://prove2.me/theorems/785a4114-3ada-4964-a08c-9346c9badfaf
-- title:
--   Eq. (3.28), Step 2 of Theorem 3.4 — ℙ(β_h < ∞) ≤ C/h²: the probability that |x(t)| ever reaches h is O(1/h²)
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma=(\gamma_{ij})$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (with constants $K_1,K_2>0$) and Assumption 2.2 (with constant $K_3>0$). Let $U\in C^{2,1}(\mathbb R^n\times S\times\mathbb R_+;\mathbb R_+)$ and $\lambda_1,\lambda_2>0$ satisfy Assumption 3.1, and let the observation interval $\tau>0$ satisfy (3.5):
--   $$\lambda_2>\frac{\tau K_3^2}{\lambda_1}\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\quad\text{and}\quad\tau\le\frac1{4K_3}.$$
--   Fix initial data $x_0\in\mathbb R^n$ and $r_0\in S$, a stochastic basis (a filtration under the usual conditions, an $m$-dimensional Brownian motion $w$ and a Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1), $dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t)$, $x(0)=x_0$, with $\delta_t=[t/\tau]\tau$.
--
--   Then there is a positive constant $C$ such that for every $h>|x_0|$,
--   $$\mathbb P\big(\beta_h<\infty\big)=\mathbb P\big(|x(t)|\ge h\ \text{for some }t\ge0\big)\le\frac C{h^2},$$
--   where $\beta_h=\inf\{t\ge0:|x(t)|\ge h\}$ (with $\inf\emptyset=\infty$). Consequently, for every $\varepsilon>0$ and all sufficiently large $h$, the event $\Omega_2=\{|x(t)|<h\text{ for all }0\le t<\infty\}$ satisfies $\mathbb P(\Omega_2)\ge1-\varepsilon$, which is (3.28).
--
--   This is Step 2 of the proof of Theorem 3.4: with high probability the whole path stays in a bounded ball.
--
--   **Formalization Note** The event $\{\beta_h<\infty\}$ is written without the stopping time, as $\{\exists t\ge0:\ |x(t)|\ge h\}$; the two coincide because $\inf\emptyset=\infty$. The constant $C$ is existential, chosen after the initial data and the solution and before $h$ (the page lets $h$ grow with $C$ fixed). The probability of the event is its outer measure, which is its probability whenever the event is measurable (as it is up to a null set, the paths being a.s. continuous). The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, pp. 914–915, Step 2 of the proof of Theorem 3.4 (display ℙ(β_h < ∞) ≤ C/h² ≤ ε and Eq. (3.28))

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Asymp_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Asymp

theorem exit_probability_bound
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
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, ‖x₀‖ < h →
      P {ω | ∃ t : ℝ≥0, h ≤ ‖x t ω‖} ≤ ENNReal.ofReal (C / h ^ 2) := by sorry

end You2015.Asymp
