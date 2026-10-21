-- Prove2me | Theorems.Thm_WrightPDIPM_CentralPath_theorem_2_8
-- name    : WrightPDIPM.CentralPath.theorem_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:53.396997+00:00
-- url     : https://prove2.me/theorems/798d911e-b6ce-4d0d-a398-79e4bf07aded
-- title:
--   Theorem 2.8 — if F° ≠ ∅ and τ > 0, f_τ has a unique local minimizer in H° and the central path conditions (2.25) have a solution
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$ (no rank assumption), $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, and let $\mathcal F^\circ = \{(x,\lambda,s) : Ax=b,\ A^{\mathsf T}\lambda + s = c,\ (x,s) > 0\}$ be the strictly feasible set of the standard-form primal-dual LP pair. Define the reduced strictly feasible set
--   $$\mathcal H^\circ = \{(x,s) \mid (x,\lambda,s) \in \mathcal F^\circ \text{ for some } \lambda \in \mathbb{R}^m\}$$
--   and, for $\tau > 0$, the primal-dual log barrier
--   $$f_\tau(x,s) = \frac1\tau\, x^{\mathsf T}s - \sum_{j=1}^n \log(x_j s_j).$$
--
--   **Theorem.** Suppose $\mathcal F^\circ \neq \emptyset$ and let $\tau > 0$. Then
--
--   1. $f_\tau$ has a unique local minimizer in $\mathcal H^\circ$: there is exactly one $(x, s) \in \mathcal H^\circ$ such that $f_\tau(x,s) \le f_\tau(x', s')$ for all $(x', s') \in \mathcal H^\circ$ in some neighbourhood of $(x,s)$;
--   2. the central path conditions (2.25) have a solution: there exist $x, s \in \mathbb{R}^n$, $\lambda \in \mathbb{R}^m$ with
--   $$A^{\mathsf T}\lambda + s = c,\qquad Ax = b,\qquad XSe = \tau e,\qquad (x,s) > 0,$$
--   where $X = \operatorname{diag}(x)$, $S = \operatorname{diag}(s)$, $e = (1,\dots,1)^{\mathsf T}$, i.e. $x_j s_j = \tau$ for every $j$.
--
--   This is the existence of the central path: for every $\tau > 0$ there is a strictly feasible point whose pairwise products $x_j s_j$ all equal $\tau$, the curve that primal-dual path-following methods track toward the solution set.
--
--   **Formalization Note** "Local minimizer in $\mathcal H^\circ$" is taken relative to $\mathcal H^\circ$ (`IsLocalMinOn`, neighbourhoods within $\mathcal H^\circ$): $\mathcal H^\circ$ is relatively open in an affine subspace and has empty interior in $\mathbb{R}^{2n}$ when $A \neq 0$, so an unrestricted local minimizer would not exist in general. $f_\tau$ is only evaluated on $\mathcal H^\circ$, where $\log(x_j s_j)$ is the true logarithm. Only existence is claimed in part 2; $\lambda$ is not unique unless $A$ has full row rank, which is not assumed.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 39, Theorem 2.8 (H° and f_τ defined p. 37, conditions (2.25) p. 36)

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP

namespace WrightPDIPM.CentralPath

open Matrix

/-- Wright, *Primal-Dual Interior-Point Methods*, SIAM 1997, p. 39, Theorem 2.8. Suppose
`F° ≠ ∅` and `τ > 0`. Then `f_τ` has a unique local minimizer in `H°` (local relative to
`H°`, which is relatively open in an affine subspace), and the central path conditions (2.25)
have a solution `(x, λ, s)`. No rank assumption on `A`; `λ` is not claimed unique. -/
theorem theorem_2_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hFo : (Fo A b c).Nonempty) (τ : ℝ) (hτ : 0 < τ) :
    (∃! q : (Fin n → ℝ) × (Fin n → ℝ), q ∈ Hcirc A b c ∧ IsLocalMinOn (ftau τ) (Hcirc A b c) q) ∧
    ∃ (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ), CentralPathConditions A b c τ x lam s := by sorry

end WrightPDIPM.CentralPath
