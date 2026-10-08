-- Prove2me | Theorems.Thm_WorstCaseCVaR_Discrete_reduction_to_interval
-- name    : WorstCaseCVaR.Discrete.reduction_to_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:04.022988+00:00
-- url     : https://prove2.me/theorems/b131dc8d-7541-40db-8aaf-9d59daffd783
-- title:
--   Proof of Theorem 2 — one bounded interval $\mathcal A$ contains a minimizer of $G_\beta(x,\cdot,\pi)$ for every $\pi \in \mathcal P_\pi$
-- statement:
--   Let $f$, the scenarios $y_{[1]},\dots,y_{[S]}$, the decision $x$ and $G_\beta$ be as in the setting of §2.2, with $0<\beta<1$, and let $\mathcal P_\pi$ be any set of probability vectors in $\mathbb R^S$. Then there is a nonempty, closed and bounded interval $\mathcal A = [a,b]$ ($a \le b$) such that for every $\pi \in \mathcal P_\pi$ the function $\alpha \mapsto G_\beta(x,\alpha,\pi)$ attains its minimum over $\mathbb R$ at some point of $\mathcal A$. Consequently, for every $\pi \in \mathcal P_\pi$,
--   $$\min_{\alpha\in\mathbb R} G_\beta(x,\alpha,\pi) = \min_{\alpha\in\mathcal A} G_\beta(x,\alpha,\pi),$$
--   and hence $\max_{\pi\in\mathcal P_\pi}\min_{\alpha\in\mathbb R} G_\beta = \max_{\pi\in\mathcal P_\pi}\min_{\alpha\in\mathcal A} G_\beta$.
--
--   This reduces the unbounded threshold variable $\alpha$ to a compact interval that does not depend on $\pi$, which is what makes a compact minimax theorem applicable in the proof of Theorem 2.
--
--   **Formalization Note** The statement is existential in $a \le b$: the interval is not fixed in the statement. "Attains its minimum over $\mathbb R$ at a point of $\mathcal A$" is `∃ α ∈ Set.Icc a b, IsMinOn (fun α' => G … α' π) Set.univ α`. The paper's preliminary remark that the bounded set $\mathcal P_\pi$ lies in a polytope spanned by finitely many distributions is its route to this fact and is not part of the statement.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Theorem 2 (first two displays)

import Mathlib
import Definitions.Def_WorstCaseCVaR_Discrete_Setting

namespace WorstCaseCVaR.Discrete

/-- Proof of Theorem 2, Zhu & Fukushima (2009), p. 1167: there is one nonempty, closed, bounded
interval `𝒜 = [a, b]` such that, for every `π ∈ 𝒫_π`, `G_β(x, ·, π)` attains its minimum over `ℝ`
at a point of `𝒜`; hence `min_{α ∈ ℝ} G_β(x, α, π) = min_{α ∈ 𝒜} G_β(x, α, π)`. -/
theorem reduction_to_interval {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) :
    ∃ a b : ℝ, a ≤ b ∧ ∀ π ∈ P, ∃ α ∈ Set.Icc a b,
      IsMinOn (fun α' : ℝ => G f ys β x α' π) Set.univ α := by sorry

end WorstCaseCVaR.Discrete
