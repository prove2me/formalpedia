-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_theorem_5_6
-- name    : WrightPDIPM.PathFollowing.theorem_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:59.363994+00:00
-- url     : https://prove2.me/theorems/ea54f2f5-2aed-42fe-8033-0990858d6164
-- title:
--   Theorem 5.6 — under (5.15) every step α ∈ [0, 1] from N₂(θ) stays in N₂(θ)
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and let the parameters $\theta \in (0,1)$ and $\sigma \in (0,1)$ satisfy
--   $$\frac{\theta^2 + n(1-\sigma)^2}{2^{3/2}(1-\theta)} \le \sigma\theta. \qquad (5.15)$$
--   Suppose $(x,\lambda,s) \in \mathcal N_2(\theta) = \{(x,\lambda,s) \in \mathcal F^\circ : \|XSe - \mu e\|_2 \le \theta\mu\}$, where $\mathcal F^\circ$ is the set of triples with $Ax = b$, $A^{\mathsf T}\lambda + s = c$, $x > 0$, $s > 0$ and $\mu = x^{\mathsf T}s/n$, and let $(\Delta x, \Delta\lambda, \Delta s)$ solve the step equations (1.12) at this point with this $\sigma$. Then
--   $$(x(\alpha), \lambda(\alpha), s(\alpha)) = (x,\lambda,s) + \alpha(\Delta x, \Delta\lambda, \Delta s) \in \mathcal N_2(\theta) \qquad\text{for all } \alpha \in [0,1].$$
--
--   In particular the full step $\alpha = 1$ keeps the iterate in the neighborhood, which is what makes the short-step path-following algorithm (with $\theta = 0.4$, $\sigma = 1 - 0.4/\sqrt n$) well defined and, with Lemma 5.1, gives its $O(\sqrt n \log(1/\epsilon))$ iteration bound.
--
--   **Formalization Note** Membership in $\mathcal N_2(\theta)$ includes strict feasibility — both equality constraints and $x(\alpha) > 0$, $s(\alpha) > 0$ — not only the proximity inequality. The direction is any solution of the linear equations (1.12); no rank assumption on $A$ is made.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 91, Theorem 5.6, Eq. (5.15)

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Theorem 5.6 (p. 91): let θ ∈ (0, 1) and σ ∈ (0, 1) satisfy
`(θ² + n(1 − σ)²)/(2^{3/2}(1 − θ)) ≤ σθ` (5.15). If `(x, λ, s) ∈ N₂(θ)` and `(Δx, Δλ, Δs)`
solves (1.12) with this σ, then `(x(α), λ(α), s(α)) = (x, λ, s) + α(Δx, Δλ, Δs) ∈ N₂(θ)` for
all α ∈ [0, 1] — including strict feasibility, since `N₂(θ) ⊆ F°`. -/
theorem theorem_5_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (θ σ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (h515 : (θ ^ 2 + (n : ℝ) * (1 - σ) ^ 2) / ((2 : ℝ) ^ ((3 : ℝ) / 2) * (1 - θ)) ≤ σ * θ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c θ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) :
    ∀ α ∈ Set.Icc (0 : ℝ) 1, (x + α • dx, lam + α • dlam, s + α • ds) ∈ N2 A b c θ := by sorry

end WrightPDIPM.PathFollowing
