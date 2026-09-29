-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_quadratic_form_nonneg_iff_posSemidef
-- name    : WorstCaseVaR.KnownMoments.quadratic_form_nonneg_iff_posSemidef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:13:23.061516+00:00
-- url     : https://prove2.me/theorems/4eb619c2-2a53-4ca1-b5d8-9c76c33f8a85
-- title:
--   §2.1, p. 546 — Condition C.1 is equivalent to $M \succeq 0$
-- statement:
--   Let $M$ be a symmetric $(n+1)\times(n+1)$ real matrix and let $l(x) = [x^\top\ 1]\, M\, [x^\top\ 1]^\top$ be the associated quadratic function on $\mathbb R^n$. Then
--
--   $$l(x) \ge 0 \ \text{ for every } x \in \mathbb R^n \quad\Longleftrightarrow\quad M \succeq 0.$$
--
--   This is Condition C.1 in the proof of Theorem 1: finiteness of the dual function of the moment problem requires $l \ge 0$ everywhere, and this lemma turns that requirement into a semidefinite constraint.
--
--   **Formalization Note.** $x$ ranges over `EuclideanSpace ℝ (Fin n)`; $M$ is indexed by `Fin n ⊕ Fin 1` and assumed symmetric (`IsSymm`), as the paper's $M = M^\top$.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 546, §2.1, proof of Theorem 1, Condition C.1 and Eq. (15)

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- Condition C.1 (p. 546): for a symmetric `(n+1) × (n+1)` matrix `M`, the quadratic function
`l(x) = [xᵀ 1] M [xᵀ 1]ᵀ` is nonnegative for every `x ∈ ℝⁿ` iff `M ⪰ 0`. -/
theorem quadratic_form_nonneg_iff_posSemidef {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (hM : M.IsSymm) :
    (∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ quadFn M ⇑x) ↔ M.PosSemidef := by sorry

end WorstCaseVaR.KnownMoments
