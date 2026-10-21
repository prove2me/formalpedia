-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_1
-- name    : WrightPDIPM.PathFollowing.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:54.757605+00:00
-- url     : https://prove2.me/theorems/0757c5a7-f6a4-4689-9dd2-ba4b64f938eb
-- title:
--   Lemma 5.1 — ΔxᵀΔs = 0 and μ(α) = (1 − α(1 − σ))μ along the step (1.12)
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, let $x, s \in \mathbb{R}^n$, let $\sigma \in [0,1]$, and let $(\Delta x, \Delta\lambda, \Delta s)$ solve the step equations (1.12) at $(x, s)$ with centering parameter $\sigma$:
--   $$A^{\mathsf T}\Delta\lambda + \Delta s = 0, \qquad A\Delta x = 0, \qquad S\Delta x + X\Delta s = -XSe + \sigma\mu e,$$
--   where $\mu = x^{\mathsf T}s/n$. For $\alpha \in \mathbb{R}$ put $x(\alpha) = x + \alpha\Delta x$, $s(\alpha) = s + \alpha\Delta s$ and $\mu(\alpha) = x(\alpha)^{\mathsf T}s(\alpha)/n$. Then
--   $$\Delta x^{\mathsf T}\Delta s = 0 \qquad\text{and}\qquad \mu(\alpha) = (1 - \alpha(1-\sigma))\mu \quad\text{for every } \alpha \in \mathbb{R}.$$
--
--   The duality measure therefore decreases linearly along any direction of the step equations; this is the source of the linear convergence of every algorithm of the chapter.
--
--   **Formalization Note** The lemma places no condition on $(x, s)$, and none is imposed. The book's range $\sigma \in [0,1]$ (p. 8) is kept as a hypothesis; $\alpha$ ranges over all reals, as (5.5) places no restriction on it. At $n = 0$ both sides of (5.7) are $0$ by Lean's convention $0/0 = 0$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 87, Lemma 5.1, Eqs. (5.6)–(5.7)

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.1 (p. 87): for a step defined by (1.12), `ΔxᵀΔs = 0` (5.6) and
`μ(α) = (1 − α(1 − σ))μ` (5.7), where `μ(α) = x(α)ᵀs(α)/n` with `x(α) = x + αΔx`,
`s(α) = s + αΔs` (5.5). The book's σ ∈ [0, 1] (p. 8) is kept; α ranges over all reals, as (5.5)
places no restriction on it. -/
theorem lemma_5_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (σ : ℝ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) :
    dx ⬝ᵥ ds = 0 ∧
      ∀ α : ℝ, mu (x + α • dx) (s + α • ds) = (1 - α * (1 - σ)) * mu x s := by sorry

end WrightPDIPM.PathFollowing
