-- Prove2me | Theorems.Thm_LinearOptimization_lp_general_weak_duality
-- name    : LinearOptimization.lp_general_weak_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T15:59:28.075222+00:00
-- url     : https://prove2.me/theorems/774c88ef-a0b5-4af7-977b-1bb764315835
-- title:
--   Weak duality with a polyhedral constraint set
-- statement:
--   **(Theorem 4.17, Weak duality — Bertsimas & Tsitsiklis, p. 184.)** Consider the primal problem: minimize $c'x$ subject to $Ax \ge b$, $x \in P$, where $P$ is the polyhedron $P = \{x \mid Dx \ge d\}$, and define the dual objective (Eq. 4.7)
--
--   $$g(p) = \min_{x \in P}\big[c'x + p'(b - Ax)\big];$$
--
--   the dual problem is: maximize $g(p)$ subject to $p \ge 0$.
--
--   If $x$ is primal feasible ($Ax \ge b$ and $x \in P$), and $p$ is dual feasible ($p \ge 0$), then
--
--   $$g(p) \le c'x.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.17, p. 184

import Definitions.Def_LinearOptimization_LagrangeanDual


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.17 (p. 184).** Weak duality for the general dual: if
`Ax ≥ b`, `x ∈ {y | Dy ≥ d}`, and `p ≥ 0`, then
`g(p) = inf_{y ∈ P} [c'y + p'(b − Ay)] ≤ c'x`. -/

theorem LinearOptimization.lp_general_weak_duality {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ)
    (x : Fin n → ℝ) (hxA : b ≤ A.mulVec x) (hxP : x ∈ polyhedron D d)
    (p : Fin m₁ → ℝ) (hp : 0 ≤ p) :
    lagrangeanObjective A b c (polyhedron D d) p ≤ ((c ⬝ᵥ x : ℝ) : EReal) := by
  sorry
