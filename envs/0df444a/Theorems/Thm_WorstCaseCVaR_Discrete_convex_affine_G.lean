-- Prove2me | Theorems.Thm_WorstCaseCVaR_Discrete_convex_affine_G
-- name    : WorstCaseCVaR.Discrete.convex_affine_G
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:47.4338+00:00
-- url     : https://prove2.me/theorems/ae090360-d3be-4973-8094-d88f8ba5877e
-- title:
--   Proof of Theorem 2 — $G_\beta(x,\alpha,\pi)$ is convex in $\alpha$ and affine in $\pi$
-- statement:
--   Let $f$, the scenarios $y_{[1]},\dots,y_{[S]}$, the decision $x$ and the function $G_\beta$ be as in the setting of §2.2, with confidence level $0<\beta<1$. Then:
--
--   1. for every probability vector $\pi$ (that is, $\pi_k \ge 0$ and $\sum_k \pi_k = 1$), the function $\alpha \mapsto G_\beta(x,\alpha,\pi)$ is convex on $\mathbb R$;
--   2. for every $\alpha \in \mathbb R$, the function $\pi \mapsto G_\beta(x,\alpha,\pi)$ is an affine function on $\mathbb R^S$:
--   $$G_\beta(x,\alpha,\pi) = \alpha + \sum_{k=1}^S \pi_k\, c_k(\alpha), \qquad c_k(\alpha) = \frac{[f(x,y_{[k]})-\alpha]^+}{1-\beta}.$$
--
--   These are the two structural properties under which the minimax lemma (Lemma 1) applies to $G_\beta$ on a product of an interval of thresholds $\alpha$ and the ambiguity set of distributions $\pi$; affinity in $\pi$ gives in particular the concavity in $\pi$ that the lemma needs.
--
--   **Formalization Note** Convexity in $\alpha$ is stated as `ConvexOn ℝ Set.univ` for each $\pi$ in `stdSimplex ℝ (Fin S)`; only $\pi \ge 0$ and $\beta < 1$ matter for it. Affinity in $\pi$ is stated as the existence of an affine map `(Fin S → ℝ) →ᵃ[ℝ] ℝ` that agrees with $G_\beta(x,\alpha,\cdot)$ everywhere.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Theorem 2 (convexity in α cited from Rockafellar and Uryasev 2002)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Discrete_Setting

namespace WorstCaseCVaR.Discrete

/-- Proof of Theorem 2, Zhu & Fukushima (2009), p. 1167: for fixed `x`, `G_β(x, α, π)` is convex
in `α` (for each probability vector `π`) and affine in `π` (for each `α`). -/
theorem convex_affine_G {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ π ∈ stdSimplex ℝ (Fin S), ConvexOn ℝ Set.univ (fun α : ℝ => G f ys β x α π)) ∧
    (∀ α : ℝ, ∃ g : (Fin S → ℝ) →ᵃ[ℝ] ℝ, ∀ π : Fin S → ℝ, G f ys β x α π = g π) := by sorry

end WorstCaseCVaR.Discrete
