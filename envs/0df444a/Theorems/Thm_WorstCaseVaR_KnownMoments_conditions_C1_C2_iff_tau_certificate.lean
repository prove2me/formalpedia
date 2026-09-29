-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_conditions_C1_C2_iff_tau_certificate
-- name    : WorstCaseVaR.KnownMoments.conditions_C1_C2_iff_tau_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:13:59.816134+00:00
-- url     : https://prove2.me/theorems/969718ea-8a03-4ccf-895b-9324e68f4d82
-- title:
--   §2.1, p. 546 — Conditions C.1, C.2 are equivalent to a $\tau$-certificate
-- statement:
--   Let $M$ be a symmetric $(n+1)\times(n+1)$ matrix with quadratic function $l(x) = [x^\top\ 1] M [x^\top\ 1]^\top$, let $w \in \mathbb R^n$ with $w \neq 0$, and let $\gamma \in \mathbb R$. Consider
--
--   - **C.1**: $l(x) \ge 0$ for every $x \in \mathbb R^n$;
--   - **C.2**: $l(x) \ge 1$ for every $x \in \mathbb R^n$ such that $\gamma + x^\top w \le 0$.
--
--   Then C.1 and C.2 hold together if and only if there is $\tau \ge 0$ with
--
--   $$M \succeq 0, \qquad M + \begin{bmatrix} 0 & \tau w \\ \tau w^\top & -1 + 2\tau\gamma \end{bmatrix} \succeq 0,$$
--
--   where the upper-left block is the $n\times n$ zero matrix.
--
--   This converts the semi-infinite conditions under which the dual function of the worst-case probability problem is finite into two linear matrix inequalities. The hypothesis $w \ne 0$ guarantees a point with $\gamma + x^\top w < 0$ (a Slater point), which the necessity direction uses.
--
--   **Formalization Note.** $x$ ranges over `EuclideanSpace ℝ (Fin n)` and $x^\top w$ is the inner product; the bordered block is `bordered 0 (τ • w) (-1 + 2τγ)`.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 546, §2.1, proof of Theorem 1, Conditions C.1, C.2 and the display following them

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- Conditions C.1 and C.2 (p. 546) are equivalent to the existence of a multiplier `τ ≥ 0`
with `M ⪰ 0` and `M + [[0, τw], [τwᵀ, -1 + 2τγ]] ⪰ 0`, for a symmetric `M` and `w ≠ 0`. -/
theorem conditions_C1_C2_iff_tau_certificate {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (hM : M.IsSymm)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) (γ : ℝ) :
    ((∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ quadFn M ⇑x) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), γ + ⟪x, w⟫_ℝ ≤ 0 → 1 ≤ quadFn M ⇑x)) ↔
      ∃ τ : ℝ, 0 ≤ τ ∧ M.PosSemidef ∧
        (M + bordered 0 (τ • ⇑w) (-1 + 2 * τ * γ)).PosSemidef := by sorry

end WorstCaseVaR.KnownMoments
