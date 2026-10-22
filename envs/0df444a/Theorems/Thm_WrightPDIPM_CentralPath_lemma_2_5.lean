-- Prove2me | Theorems.Thm_WrightPDIPM_CentralPath_lemma_2_5
-- name    : WrightPDIPM.CentralPath.lemma_2_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:59.924209+00:00
-- url     : https://prove2.me/theorems/b942ec5b-c6ea-4f74-9dd3-2c7d7693aeae
-- title:
--   Lemma 2.5 — if F° ≠ ∅, the feasible (x, s) with xᵀs ≤ K form a bounded set
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$ (arbitrary), $b \in \mathbb{R}^m$, $c\in\mathbb{R}^n$, and let $\mathcal F$, $\mathcal F^\circ$ be the primal-dual feasible and strictly feasible sets of the standard-form LP pair: $\mathcal F = \{(x,\lambda,s) : Ax=b,\ A^{\mathsf T}\lambda + s = c,\ (x,s)\ge 0\}$, and $\mathcal F^\circ$ the same with $(x,s) > 0$. Suppose $\mathcal F^\circ \neq \emptyset$. Then for each $K \ge 0$ the set
--
--   $$\{(x, s) \mid (x,\lambda,s) \in \mathcal F \text{ for some } \lambda, \text{ and } x^{\mathsf T}s \le K\}$$
--
--   is bounded.
--
--   The lemma is the compactness ingredient in the proof that the central path exists: it bounds the level sets of the primal-dual barrier.
--
--   **Formalization Note** "Bounded" is `Bornology.IsBounded` for pairs $(x, s) \in \mathbb{R}^n \times \mathbb{R}^n$ (independent of the norm). The book's hypothesis $K \ge 0$ is kept.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 30, Lemma 2.5

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP

namespace WrightPDIPM.CentralPath

open Matrix

/-- Wright, *Primal-Dual Interior-Point Methods*, SIAM 1997, p. 30, Lemma 2.5. Suppose
`F° ≠ ∅`. Then for each `K ≥ 0` the set
`{(x, s) | (x, λ, s) ∈ F for some λ, and xᵀs ≤ K}` is bounded. -/
theorem lemma_2_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hFo : (Fo A b c).Nonempty) (K : ℝ) (hK : 0 ≤ K) :
    Bornology.IsBounded
      {q : (Fin n → ℝ) × (Fin n → ℝ) | ∃ lam, (q.1, lam, q.2) ∈ F A b c ∧ q.1 ⬝ᵥ q.2 ≤ K} := by sorry

end WrightPDIPM.CentralPath
