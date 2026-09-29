-- Prove2me | Theorems.Thm_You2015_Asymp_sampling_error_moment_bound
-- name    : You2015.Asymp.sampling_error_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:34:23.602516+00:00
-- url     : https://prove2.me/theorems/cb6af20d-f75a-477b-9b2f-ca39be8239d1
-- title:
--   Eq. (3.21) — 𝔼|x(s) − x(δ_s)|² ≤ 3(τK₁² + K₂²)/(1 − 6τ²K₃²) ∫_{δ_s}^s 𝔼|x(z)|² dz + 6τ²K₃²/(1 − 6τ²K₃²) 𝔼|x(s)|²
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (constants $K_1,K_2>0$) and Assumption 2.2 (constant $K_3>0$), and let $\tau>0$ with $\tau\le1/(4K_3)$. Fix $x_0\in\mathbb R^n$, $r_0\in S$, a stochastic basis (filtration under the usual conditions, $m$-dimensional Brownian motion $w$, Markov chain $r$ with generator $\Gamma$, $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1) with $x(0)=x_0$ and sampling times $\delta_t=[t/\tau]\tau$.
--
--   Then $6\tau^2K_3^2<1$ and for every $s\ge0$,
--   $$\mathbb E|x(s)-x(\delta_s)|^2\le\frac{3(\tau K_1^2+K_2^2)}{1-6\tau^2K_3^2}\int_{\delta_s}^s\mathbb E|x(z)|^2dz+\frac{6\tau^2K_3^2}{1-6\tau^2K_3^2}\,\mathbb E|x(s)|^2.\tag{3.21}$$
--
--   This bounds the mean-square sampling error by the second moment of the state itself; it is the step that turns $H_\infty$-stability (Theorem 3.2) into a uniform bound on $\mathbb E|x(t)|^2$ (3.23).
--
--   **Formalization Note** The page derives (3.21) in the proof of Theorem 3.3, noting that "$6\tau^2K_3^2<1$ by condition (3.5)". That inequality comes from the second half of (3.5), $\tau\le1/(4K_3)$, which gives $6\tau^2K_3^2\le3/8$; the derivation uses only Assumptions 2.1 and 2.2 besides. The statement is therefore made under Assumptions 2.1, 2.2, $\tau>0$ and $\tau\le1/(4K_3)$, which is stronger than on the page. Both fractions are positive reals; the inequality holds in $[0,\infty]$. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 913, Eq. (3.21) (in the proof of Theorem 3.3)

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Asymp_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Asymp

theorem sampling_error_moment_bound
    {n m N : ℕ} (Γ : Matrix (Fin N) (Fin N) ℝ) (hΓ : You2015.Shared.IsGenerator Γ)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (K₁ K₂ K₃ : ℝ) (h21 : Assumption21 f g K₁ K₂) (h22 : Assumption22 u K₃)
    (τ : ℝ≥0) (hτ : 0 < τ)
    (hτK₃ : (τ : ℝ) ≤ 1 / (4 * K₃))
    (x₀ : EuclideanSpace ℝ (Fin n)) (r₀ : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : You2015.Shared.HybridSetup P m N Γ r₀) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n))
    (hx : You2015.Shared.SolvesSampledHybridSDE S f u g τ x₀ x) :
    ∀ s : ℝ≥0, ∫⁻ ω, ‖x s ω - x (You2015.Shared.delta τ s) ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (3 * (τ * K₁ ^ 2 + K₂ ^ 2) / (1 - 6 * τ ^ 2 * K₃ ^ 2))
          * ∫⁻ z in Set.Icc (You2015.Shared.delta τ s : ℝ) s, ∫⁻ ω, ‖x z.toNNReal ω‖ₑ ^ 2 ∂P
        + ENNReal.ofReal (6 * τ ^ 2 * K₃ ^ 2 / (1 - 6 * τ ^ 2 * K₃ ^ 2))
          * ∫⁻ ω, ‖x s ω‖ₑ ^ 2 ∂P := by sorry

end You2015.Asymp
