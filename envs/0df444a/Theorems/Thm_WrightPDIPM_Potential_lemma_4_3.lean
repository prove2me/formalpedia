-- Prove2me | Theorems.Thm_WrightPDIPM_Potential_lemma_4_3
-- name    : WrightPDIPM.Potential.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:08.112497+00:00
-- url     : https://prove2.me/theorems/b6e0ad58-1154-4c7f-99b5-8057ef776f85
-- title:
--   Lemma 4.3 — Φ_ρ is unbounded below on its domain, and μ ≤ exp(Φ_ρ(x, s)/(ρ − n)) on F°
-- statement:
--   Let $A \in \mathbb R^{m\times n}$ with $n \ge 1$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, let $\mathcal F^\circ$ be the strictly feasible set of the primal-dual pair, and let $\rho > n$.
--
--   1. If $\mathcal F^\circ \ne \emptyset$, the potential $\Phi_\rho(x,s) = \rho\log x^Ts - \sum_i\log x_is_i$ is unbounded below on its domain $\{(x,s) : (x,\lambda,s) \in \mathcal F^\circ \text{ for some } \lambda\}$: for every $M$ there is $(x,\lambda,s) \in \mathcal F^\circ$ with $\Phi_\rho(x,s) < M$.
--   2. For every $(x,\lambda,s) \in \mathcal F^\circ$, with $\mu = x^Ts/n$,
--   $$\mu \le \exp\big(\Phi_\rho(x,s)/(\rho - n)\big). \qquad (4.7)$$
--
--   Part 2 is the link between the potential and the duality measure: driving $\Phi_\rho$ to $-\infty$ drives $\mu$ to $0$.
--
--   **Formalization Note** The book states $\rho > n$ once, with the definition (4.2), and assumes $n \ge 1$ throughout; both are hypotheses here. Part 1 assumes $\mathcal F^\circ \ne \emptyset$, which the book's proof uses through the existence of the central path (Theorem 2.8) and which is necessary: on an empty domain nothing is unbounded below.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 69, Lemma 4.3

import Mathlib
import Definitions.Def_WrightPDIPM_Potential_Setting

open Matrix

namespace WrightPDIPM.Potential

/-- **Lemma 4.3** (Wright, p. 69), for `ρ > n` (the range of the parameter in (4.2)) and
`n ≥ 1`.
(i) If `F° ≠ ∅`, `Φ_ρ` is unbounded below on its domain (4.3), the pairs `(x, s)` with
`(x, λ, s) ∈ F°` for some `λ`. (The proof uses the central path, which exists when
`F° ≠ ∅`.)
(ii) For any `(x, λ, s) ∈ F°`, `μ ≤ exp(Φ_ρ(x, s)/(ρ − n))` (4.7), where `μ = xᵀs/n`. -/
theorem lemma_4_3 {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (n : ℝ) < ρ) :
    ((Fo A b c).Nonempty →
      ∀ M : ℝ, ∃ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ),
        (x, lam, s) ∈ Fo A b c ∧ Phi ρ x s < M) ∧
    (∀ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ), (x, lam, s) ∈ Fo A b c →
      mu x s ≤ Real.exp (Phi ρ x s / (ρ - n))) := by sorry

end WrightPDIPM.Potential
