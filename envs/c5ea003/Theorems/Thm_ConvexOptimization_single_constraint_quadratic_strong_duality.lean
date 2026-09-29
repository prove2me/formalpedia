-- Prove2me | Theorems.Thm_ConvexOptimization_single_constraint_quadratic_strong_duality
-- name    : ConvexOptimization.single_constraint_quadratic_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:05:26.896448+00:00
-- url     : https://prove2.me/theorems/625b8369-8881-4fc3-8427-465bc29f31ac
-- title:
--   Trust-region strong duality (level-set form)
-- statement:
--   **Zero duality gap for minimizing one quadratic function subject to another** — the strong-duality result of B&V §B.1.
--
--   Let $q_k(x) = x^{T}A_k x + 2b_k^{T}x + c_k$ for $k = 0, 1$ with $A_0, A_1$ symmetric, and assume strict feasibility: some $\hat{x}$ has $q_1(\hat{x}) < 0$. Then for every $\gamma \in \mathbb{R}$,
--
--   $$\bigl(q_1(x) \le 0 \Rightarrow q_0(x) \ge \gamma \ \text{ for all } x\bigr) \qquad\Longleftrightarrow\qquad \exists\,\lambda \ge 0:\ \begin{bmatrix} A_0 & b_0 \\ b_0^{T} & c_0 - \gamma\end{bmatrix} + \lambda \begin{bmatrix} A_1 & b_1 \\ b_1^{T} & c_1 \end{bmatrix} \;\succeq\; 0 .$$
--
--   Read as an optimization statement: $\gamma$ is a lower bound for the (generally **nonconvex**) problem of minimizing $q_0$ subject to $q_1 \le 0$ exactly when it is achievable by the semidefinite relaxation, so the two optimal values coincide and the Lagrangian relaxation is tight. This is remarkable — the primal problem need not be convex, $A_0$ and $A_1$ may be indefinite — and it is the theoretical basis of trust-region methods, where a quadratic model is minimized over a ball.
--
--   **Formalization Note** The quadratics and their block matrices are the mission's `quadForm` and `symQuadBlock`; the matrix inequality is `PosSemidef` of the sum. The statement is corrected for the factor-of-two slips in the printed eq. (B.5). In the book this result is *derived from* the S-procedure (§B.4), so it is a consequence of the mission's goal rather than a step toward it. Source: B&V §B.1, p. 654, proof in §B.4, p. 658.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 653-654, 658, §B.1 eq. (B.1)-(B.2) (strong duality for one quadratic function constrained by another), proof in §B.4. Formalized with the printed factor-of-2 slips in eq. (B.5) corrected. Note the book derives this result FROM the S-procedure, so it is a corollary of this mission's goal

import Mathlib
import Definitions.Def_ConvexOptimization_quadraticForms

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.single_constraint_quadratic_strong_duality {nn : ℕ}
    (A₀ A₁ : Matrix (Fin nn) (Fin nn) ℝ) (hA₀ : A₀.IsSymm) (hA₁ : A₁.IsSymm)
    (b₀ b₁ : Fin nn → ℝ) (c₀ c₁ : ℝ)
    (xh : Fin nn → ℝ) (hxh : quadForm A₁ b₁ c₁ xh < 0) (γ : ℝ) :
    (∀ x, quadForm A₁ b₁ c₁ x ≤ 0 → γ ≤ quadForm A₀ b₀ c₀ x) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (symQuadBlock A₀ b₀ (c₀ - γ) + lam • symQuadBlock A₁ b₁ c₁).PosSemidef := by
  sorry
