-- Prove2me | Theorems.Thm_WorstCaseCVaR_Discrete_lemma_1_on_interval
-- name    : WorstCaseCVaR.Discrete.lemma_1_on_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:36.116987+00:00
-- url     : https://prove2.me/theorems/e29638eb-8058-4f77-ba2f-1e56c59b624b
-- title:
--   Proof of Theorem 2 — Lemma 1 on $\mathcal A \times \mathcal P_\pi$: $\max_\pi\min_{\alpha\in\mathcal A} G_\beta = \min_{\alpha\in\mathcal A}\max_\pi G_\beta$
-- statement:
--   Let $f$, the scenarios $y_{[1]},\dots,y_{[S]}$, the decision $x$ and $G_\beta$ be as in the setting of §2.2, with $0<\beta<1$. Let $\mathcal P_\pi \subseteq \mathbb R^S$ be a nonempty compact convex set of probability vectors and let $\mathcal A = [a,b]$ with $a \le b$ be a nonempty closed bounded interval. Then $G_\beta(x,\cdot,\cdot)$ has a saddle point $(\alpha_0,\pi_0) \in \mathcal A \times \mathcal P_\pi$:
--   $$G_\beta(x,\alpha_0,\pi) \le G_\beta(x,\alpha_0,\pi_0) \le G_\beta(x,\alpha,\pi_0)\qquad\text{for all } \alpha\in\mathcal A,\ \pi\in\mathcal P_\pi,$$
--   so that
--   $$\max_{\pi\in\mathcal P_\pi}\min_{\alpha\in\mathcal A} G_\beta(x,\alpha,\pi) = \min_{\alpha\in\mathcal A}\max_{\pi\in\mathcal P_\pi} G_\beta(x,\alpha,\pi),$$
--   all extrema being attained.
--
--   This is the exchange of minimization and maximization on the compact product $\mathcal A \times \mathcal P_\pi$, the central step of the proof of Theorem 2.
--
--   **Formalization Note** The interval is arbitrary ($a\le b$), not the specific interval produced by the reduction step; the statement is the saddle-point form of the attained min–max equality.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Theorem 2 ("By Lemma 1, we get …")

import Mathlib
import Definitions.Def_WorstCaseCVaR_Discrete_Setting

namespace WorstCaseCVaR.Discrete

/-- Proof of Theorem 2, Zhu & Fukushima (2009), p. 1167 (Lemma 1 applied on `𝒜 × 𝒫_π`): for every
nonempty closed bounded interval `𝒜 = [a, b]` and every nonempty compact convex set `𝒫_π` of
probability vectors, `G_β(x, ·, ·)` has a saddle point `(α₀, π₀)` on `𝒜 × 𝒫_π`; equivalently,
`max_{π ∈ 𝒫_π} min_{α ∈ 𝒜} G_β(x, α, π) = min_{α ∈ 𝒜} max_{π ∈ 𝒫_π} G_β(x, α, π)` with all extrema
attained. -/
theorem lemma_1_on_interval {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty)
    (hcpt : IsCompact P) (hcvx : Convex ℝ P) (a b : ℝ) (hab : a ≤ b) :
    ∃ α₀ ∈ Set.Icc a b, ∃ π₀ ∈ P, ∀ α ∈ Set.Icc a b, ∀ π ∈ P,
      G f ys β x α₀ π ≤ G f ys β x α₀ π₀ ∧ G f ys β x α₀ π₀ ≤ G f ys β x α π₀ := by sorry

end WorstCaseCVaR.Discrete
