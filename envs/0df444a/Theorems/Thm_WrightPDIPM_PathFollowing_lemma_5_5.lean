-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_5
-- name    : WrightPDIPM.PathFollowing.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:59.572172+00:00
-- url     : https://prove2.me/theorems/14d060ce-fa51-49e5-b8b9-7dcc97262424
-- title:
--   Lemma 5.5 — the centrality ‖X(α)S(α)e − μ(α)e‖ along the step from N₂(θ), (5.14a)–(5.14b)
-- statement:
--   Let $A, b, c$ be LP data, $\theta \in (0,1)$, $\sigma \in [0,1]$, $(x,\lambda,s) \in \mathcal N_2(\theta)$ and let $(\Delta x,\Delta\lambda,\Delta s)$ solve the step equations (1.12) at this point with centering parameter $\sigma$. For $\alpha \in \mathbb{R}$ let $x(\alpha) = x + \alpha\Delta x$, $s(\alpha) = s + \alpha\Delta s$, $\mu(\alpha) = x(\alpha)^{\mathsf T}s(\alpha)/n$, and $X(\alpha) = \operatorname{diag}(x(\alpha))$, $S(\alpha) = \operatorname{diag}(s(\alpha))$. Then
--   $$\begin{aligned}\|X(\alpha)S(\alpha)e - \mu(\alpha)e\|_2 &\le |1-\alpha|\,\|XSe - \mu e\|_2 + \alpha^2\|\Delta X\Delta S e\|_2 &(5.14\text{a})\\ &\le |1-\alpha|\,\theta\mu + \alpha^2\,\frac{\theta^2 + n(1-\sigma)^2}{2^{3/2}(1-\theta)}\,\mu. &(5.14\text{b})\end{aligned}$$
--
--   The lemma measures how far the point moves from the central path, in the 2-norm, as one travels along the direction.
--
--   **Formalization Note** The chain is stated as the conjunction of its two inequalities. The page leaves $\alpha$ unrestricted (it writes $|1-\alpha|$), so $\alpha$ ranges over all reals; $\theta \in (0,1)$ and $\sigma \in [0,1]$ are the standing ranges of (1.15) and (1.12).
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 90, Lemma 5.5, Eqs. (5.14a)–(5.14b)

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.5 (p. 90): if `(x, λ, s) ∈ N₂(θ)` and `(Δx, Δλ, Δs)` solves (1.12) with centering
parameter σ, then for `x(α) = x + αΔx`, `s(α) = s + αΔs`, `μ(α) = x(α)ᵀs(α)/n`:
`‖X(α)S(α)e − μ(α)e‖ ≤ |1 − α| ‖XSe − μe‖ + α²‖ΔXΔSe‖` (5.14a)
`≤ |1 − α|θμ + α²[(θ² + n(1 − σ)²)/(2^{3/2}(1 − θ))]μ` (5.14b).
θ ∈ (0, 1) and σ ∈ [0, 1] are the book's standing ranges; α ranges over all reals. -/
theorem lemma_5_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (θ σ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hN : (x, lam, s) ∈ N2 A b c θ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (hstep : IsStep A x s σ dx dlam ds) (α : ℝ) :
    norm2 (fun i => (x + α • dx) i * (s + α • ds) i - mu (x + α • dx) (s + α • ds)) ≤
        |1 - α| * norm2 (fun i => x i * s i - mu x s) + α ^ 2 * norm2 (fun i => dx i * ds i) ∧
      |1 - α| * norm2 (fun i => x i * s i - mu x s) + α ^ 2 * norm2 (fun i => dx i * ds i) ≤
        |1 - α| * θ * mu x s +
          α ^ 2 * ((θ ^ 2 + (n : ℝ) * (1 - σ) ^ 2) / ((2 : ℝ) ^ ((3 : ℝ) / 2) * (1 - θ))) *
            mu x s := by sorry

end WrightPDIPM.PathFollowing
