-- Prove2me | Theorems.Thm_You2015_Expo_vbar_bound
-- name    : You2015.Expo.vbar_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:13:01.051513+00:00
-- url     : https://prove2.me/theorems/83f50d4e-f29b-4713-88d2-d2def8373bc4
-- title:
--   Eq. (4.11) — for z ≥ 2τ, 𝔼V̄(x̂_z, r̂_z, z) ≤ (H₁ + τH₂)∫_{z−2τ}^z 𝔼|x(y)|² dy
-- statement:
--   **Setting.** Let $S=\{1,\dots,N\}$ and let $\Gamma=(\gamma_{ij})$ be a generator on $S$. Let $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$ satisfy Assumption 2.1 (constants $K_1,K_2>0$) and Assumption 2.2 (constant $K_3>0$). Let $U\in C^{2,1}(\mathbb R^n\times S\times\mathbb R_+;\mathbb R_+)$ and $\lambda_1,\lambda_2>0$ satisfy Assumption 3.1, and let the observation interval $\tau>0$ satisfy (3.5):
--   $$\lambda_2>\frac{\tau K_3^2}{\lambda_1}\big[2\tau(K_1^2+2K_3^2)+K_2^2\big]\quad\text{and}\quad\tau\le\frac1{4K_3}.$$
--   Fix initial data $x_0\in\mathbb R^n$ and $r_0\in S$, a stochastic basis (a filtration under the usual conditions, an $m$-dimensional Brownian motion $w$ and a Markov chain $r$ with generator $\Gamma$ and $r(0)=r_0$, independent of $w$), and let $x$ be any solution of the controlled system (2.1), $dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t)$, $x(0)=x_0$, with $\delta_t=[t/\tau]\tau$.
--   Write
--   $$\theta=\frac{K_3^2}{\lambda_1},\qquad\lambda=\lambda_2-\theta\tau\big[2\tau(K_1^2+2K_3^2)+K_2^2\big],$$
--   $$H_1=\theta\tau\big(2\tau(K_1^2+2K_3^2)+K_2^2\big)+\frac{24\,\theta\tau^4K_3^4}{1-6\tau^2K_3^2},\qquad H_2=\frac{12\theta\tau^2K_3^2(\tau K_1^2+K_2^2)}{1-6\tau^2K_3^2}.$$
--   Let $\bar V$ be the functional (4.7) with this $\theta$. Then for every $z\ge2\tau$,
--   $$\mathbb E\,\bar V(\hat x_z,\hat r_z,z)\le(H_1+\tau H_2)\int_{z-2\tau}^z\mathbb E|x(y)|^2\,dy.\tag{4.11}$$
--
--   This bounds the delay part of the Lyapunov–Krasovskii functional by a windowed integral of the second moment; it is what lets the Itô-formula estimate (4.6) close in the proof of Theorem 4.2.
--
--   **Formalization Note** The constant $H_1$ is the one the paper's proof of Theorem 4.2 actually uses: combining (4.9) with (3.21), the coefficient of $\int\mathbb E|x(v)|^2dv$ is $\theta\tau(2\tau(K_1^2+2K_3^2)+K_2^2)+\theta\tau\cdot4\tau K_3^2\cdot\frac{6\tau^2K_3^2}{1-6\tau^2K_3^2}$. The page prints $24\tau^3K_3^4$ in place of $24\theta\tau^4K_3^4$ in (4.5), dropping the factor $\theta\tau$; this statement uses the corrected value. The page's remark that $\mathbb E\bar V$ is bounded on $[0,2\tau]$ is not part of this statement. $\bar V\ge0$, so its expectation is a lower Lebesgue integral in $[0,\infty]$, and the inequality holds there; $H_1+\tau H_2\ge0$. The paper's "the solution" is read as "every solution" in the sense of the mission's solution definition (existence and uniqueness are cited from Mao–Yuan [23] on p. 908 and are not part of the statement). $|x|$ is the Euclidean norm and $|g|$ the trace norm, $|g|^2=\sum_k|g_k|^2$ over the columns. Expectations are lower Lebesgue integrals with values in $[0,\infty]$, so no integrability side condition is hidden in them.
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 918, Eq. (4.11) (in the proof of Theorem 4.2), with (4.7) and (4.5); H₁ corrected

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito
import Definitions.Def_You2015_Shared_Solution
import Definitions.Def_You2015_Expo_Assumptions
import Definitions.Def_You2015_Expo_Constants
import Definitions.Def_You2015_Expo_Vbar

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Expo

theorem vbar_bound
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
    ∀ z : ℝ≥0, 2 * τ ≤ z →
      ∫⁻ ω, Vbar S f u g τ (theta K₃ lam₁) x z ω ∂P ≤
        ENNReal.ofReal (H1 K₁ K₂ K₃ lam₁ τ + τ * H2 K₁ K₂ K₃ lam₁ τ)
          * ∫⁻ y in Set.Icc ((z : ℝ) - 2 * τ) z, ∫⁻ ω, ‖x y.toNNReal ω‖ₑ ^ 2 ∂P := by sorry

end You2015.Expo
