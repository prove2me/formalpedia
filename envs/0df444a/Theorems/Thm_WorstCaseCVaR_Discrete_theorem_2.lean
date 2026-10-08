-- Prove2me | Theorems.Thm_WorstCaseCVaR_Discrete_theorem_2
-- name    : WorstCaseCVaR.Discrete.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:51.036654+00:00
-- url     : https://prove2.me/theorems/62627588-64de-4a0a-91f8-0f15e477f5f1
-- title:
--   Theorem 2 — for a compact convex set $\mathcal P_\pi$ of discrete distributions, $\mathrm{WCVaR}_\beta(x) = \min_{\alpha}\max_{\pi\in\mathcal P_\pi} G_\beta(x,\alpha,\pi)$
-- statement:
--   Let $f(x,y)$ be a loss, let $y_{[1]},\dots,y_{[S]} \in \mathbb R^m$ be the scenarios of a discrete random vector, and let $0<\beta<1$ be a confidence level. For a probability vector $\pi \in \mathbb R^S$ put
--   $$G_\beta(x,\alpha,\pi) = \alpha + \frac{1}{1-\beta}\sum_{k=1}^S \pi_k\,[f(x,y_{[k]})-\alpha]^+,\qquad \mathrm{CVaR}_\beta(x,\pi) = \min_{\alpha\in\mathbb R} G_\beta(x,\alpha,\pi),$$
--   and for a set $\mathcal P_\pi$ of probability vectors let $\mathrm{WCVaR}_\beta(x) = \sup_{\pi\in\mathcal P_\pi}\mathrm{CVaR}_\beta(x,\pi)$.
--
--   **Theorem.** Suppose that $\mathcal P_\pi$ is a nonempty compact convex set of probability vectors. Then for each $x$,
--   $$\mathrm{WCVaR}_\beta(x) = \min_{\alpha\in\mathbb R}\max_{\pi\in\mathcal P_\pi} G_\beta(x,\alpha,\pi).$$
--   Both extrema on the right-hand side are attained: for every $\alpha$ the maximum over $\mathcal P_\pi$ exists, and some $\alpha_0 \in \mathbb R$ minimizes $\alpha \mapsto \max_{\pi\in\mathcal P_\pi} G_\beta(x,\alpha,\pi)$.
--
--   The theorem turns the worst-case CVaR — a supremum over distributions of a minimum over thresholds — into a minimum over the threshold of a worst case of a function that is affine in $\pi$. Minimizing $\mathrm{WCVaR}_\beta(x)$ over decisions therefore becomes the single minimization problem (16)–(20) in $(x,u,\alpha,\theta)$, which is a linear program under box uncertainty and a second-order cone program under ellipsoidal uncertainty.
--
--   **Formalization Note** The paper's hypothesis "$\mathcal P_\pi$ is a compact convex set" is completed by the standing assumptions of §2.2: its elements are probability vectors ($\pi_k\ge0$, $\sum_k\pi_k=1$, i.e. $\mathcal P_\pi \subseteq$ `stdSimplex ℝ (Fin S)`) and it is nonempty (a supremum over the empty set is meaningless). The confidence level satisfies $0<\beta<1$. The left-hand side stays a supremum, as printed. The inner maximum is stated as `IsMaxOn` and its value is used as the real `sSup` of the image of $\mathcal P_\pi$; the outer minimum is an explicit minimizer `α₀` with `IsMinOn … Set.univ`.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1159, Theorem 2 (proof p. 1167)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Discrete_Setting

namespace WorstCaseCVaR.Discrete

/-- Theorem 2, Zhu & Fukushima (2009), p. 1159: if `𝒫_π` is a compact convex set (of probability
vectors on the scenarios `y_[1], …, y_[S]`, nonempty), then for each `x`
`WCVaR_β(x) = min_{α ∈ ℝ} max_{π ∈ 𝒫_π} G_β(x, α, π)`.
Both extrema on the right are attained: for every `α` the maximum over `𝒫_π` is attained, and
some `α₀` minimizes `α ↦ max_{π ∈ 𝒫_π} G_β(x, α, π)` over `ℝ`, with value `WCVaR_β(x)`. -/
theorem theorem_2 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty)
    (hcpt : IsCompact P) (hcvx : Convex ℝ P) :
    (∀ α : ℝ, ∃ π₀ ∈ P, IsMaxOn (fun π => G f ys β x α π) P π₀) ∧
    ∃ α₀ : ℝ, IsMinOn (fun α : ℝ => sSup ((fun π => G f ys β x α π) '' P)) Set.univ α₀ ∧
      wcvar f ys β x P = sSup ((fun π => G f ys β x α₀ π) '' P) := by sorry

end WorstCaseCVaR.Discrete
