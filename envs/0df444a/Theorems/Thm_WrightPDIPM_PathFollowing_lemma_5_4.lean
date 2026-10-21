-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_4
-- name    : WrightPDIPM.PathFollowing.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:01.101315+00:00
-- url     : https://prove2.me/theorems/9c6b5390-1e9a-4cef-8b55-9e8d2cfc07b3
-- title:
--   Lemma 5.4 — ‖ΔXΔSe‖ ≤ (θ² + n(1 − σ)²)μ/(2^{3/2}(1 − θ)) in N₂(θ)
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, $\theta \in (0,1)$ and $\sigma \in [0,1]$. Suppose $(x,\lambda,s) \in \mathcal N_2(\theta)$, that is, $(x, \lambda, s)$ is strictly feasible and $\|XSe - \mu e\|_2 \le \theta\mu$ with $\mu = x^{\mathsf T}s/n$, and let $(\Delta x, \Delta\lambda, \Delta s)$ solve the step equations (1.12) at this point with centering parameter $\sigma$. Writing $\Delta X\Delta S e$ for the vector with entries $\Delta x_i\Delta s_i$,
--   $$\|\Delta X \Delta S e\|_2 \le \frac{\theta^2 + n(1-\sigma)^2}{2^{3/2}(1-\theta)}\,\mu .$$
--
--   The second-order term $\Delta X\Delta S e$ is the only part of the update of the pairwise products $x_i s_i$ that the linearized step does not control; this bound is what lets a short step stay in $\mathcal N_2(\theta)$.
--
--   **Formalization Note** The page gives no range for $\theta$ and $\sigma$ in this lemma; the standing ranges $\theta \in (0,1)$ of (1.15) and $\sigma \in [0,1]$ of (1.12) are stated as hypotheses.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 89, Lemma 5.4

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.4 (p. 89): if `(x, λ, s) ∈ N₂(θ)` and `(Δx, Δλ, Δs)` solves (1.12) with centering
parameter σ, then `‖ΔXΔSe‖ ≤ ((θ² + n(1 − σ)²)/(2^{3/2}(1 − θ))) μ`. The ranges θ ∈ (0, 1)
(from (1.15)) and σ ∈ [0, 1] (from (1.12)) are the book's standing ones. -/
theorem lemma_5_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (θ σ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c θ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) :
    norm2 (fun i => dx i * ds i) ≤
      (θ ^ 2 + (n : ℝ) * (1 - σ) ^ 2) / ((2 : ℝ) ^ ((3 : ℝ) / 2) * (1 - θ)) * mu x s := by sorry

end WrightPDIPM.PathFollowing
