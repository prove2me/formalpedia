-- Prove2me | Theorems.Thm_You2015_Expo_sampling_error_bound
-- name    : You2015.Expo.sampling_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:10:56.287986+00:00
-- url     : https://prove2.me/theorems/e32e8055-2775-42dd-a6c1-f954ab926231
-- title:
--   Eq. (3.15) — sampling-error bound 𝔼|x(t) − x(δ_t)|² ≤ 2𝔼∫_{δ_t}^t [τ|f + u(x(δ_s))|² + |g|²] ds
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (constants $K_1,K_2>0$) and Assumption 2.2 (constant $K_3>0$), and let $\tau>0$. Fix $x_0\in\mathbb R^n$, $r_0\in S$, a stochastic basis (filtration under the usual conditions, $m$-dimensional Brownian motion $w$, Markov chain $r$ with generator $\Gamma$, $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1) with $x(0)=x_0$ and sampling times $\delta_t=[t/\tau]\tau$.
--
--   Then for every $t\ge0$,
--   $$\mathbb E|x(t)-x(\delta_t)|^2\le2\,\mathbb E\int_{\delta_t}^t\Big[\tau\big|f(x(s),r(s),s)+u(x(\delta_s),r(s),s)\big|^2+\big|g(x(s),r(s),s)\big|^2\Big]ds.$$
--
--   This estimate controls the error made by feeding back the last observed state $x(\delta_t)$ instead of the current state $x(t)$; it is the first step of the proof of Theorem 3.2.
--
--   **Formalization Note** The paper derives (3.15) inside the proof of Theorem 3.2, under that theorem's hypotheses. The derivation ("noting that $t-\delta_t\le\tau$ … from (2.1)") uses only the equation, $\tau>0$ and the Itô isometry, so it is stated here under Assumptions 2.1, 2.2 and $\tau>0$ only; this is a stronger statement than the one on the page. Both sides are in $[0,\infty]$. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 911, Eq. (3.15) (in the proof of Theorem 3.2)

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Expo_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Expo

theorem sampling_error_bound
    {n m N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) (hΓ : You2015.Shared.IsGenerator Γ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ K₃ : ℝ) (h21 : Assumption21 f g K₁ K₂) (h22 : Assumption22 u K₃)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r₀ : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : You2015.Shared.HybridSetup P m N Γ r₀) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hx : You2015.Shared.SolvesSampledHybridSDE S f u g τ x₀ x) :
    ∀ t : ℝ≥0, ∫⁻ ω, ‖x t ω - x (You2015.Shared.delta τ t) ω‖ₑ ^ 2 ∂P ≤
      2 * ∫⁻ ω, ∫⁻ s in Set.Icc (You2015.Shared.delta τ t : ℝ) t,
        ((τ : ℝ≥0∞) * ‖(f (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal + u (x (You2015.Shared.delta τ s.toNNReal) ω) (S.r s.toNNReal ω) s.toNNReal)‖ₑ ^ 2
          + ∑ k, ‖(g (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal k)‖ₑ ^ 2) ∂volume ∂P := by sorry

end You2015.Expo
