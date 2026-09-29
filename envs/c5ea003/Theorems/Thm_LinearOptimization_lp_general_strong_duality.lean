-- Prove2me | Theorems.Thm_LinearOptimization_lp_general_strong_duality
-- name    : LinearOptimization.lp_general_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T15:59:39.670109+00:00
-- url     : https://prove2.me/theorems/dc5e6af5-fb1a-404d-9413-79f191c2d9d1
-- title:
--   Strong duality with a polyhedral constraint set
-- statement:
--   **(Theorem 4.18, Strong duality — Bertsimas & Tsitsiklis, p. 184.)** With the same setup as Theorem 4.17 (primal: minimize $c'x$ subject to $Ax \ge b$, $x \in P$ with $P = \{x \mid Dx \ge d\}$; dual: maximize $g(p) = \min_{x \in P}[c'x + p'(b - Ax)]$ subject to $p \ge 0$):
--
--   if the primal problem has an optimal solution, so does the dual, and the respective optimal costs are equal.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.18, p. 184

import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_LagrangeanDual


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.18 (p. 184).** Strong duality for the general dual,
attainment form: if `x*` is optimal for `min c'x` over
`{y | Ay ≥ b, y ∈ P}` (`P = {y | Dy ≥ d}`), then some `p ≥ 0` maximizes
`g` over the nonnegative orthant and `g(p) = c'x*`. -/

theorem LinearOptimization.lp_general_strong_duality {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ)
    (xstar : Fin n → ℝ)
    (hopt : IsLpOptimal c {y | b ≤ A.mulVec y ∧ y ∈ polyhedron D d} xstar) :
    ∃ p : Fin m₁ → ℝ, 0 ≤ p ∧
      (∀ q : Fin m₁ → ℝ, 0 ≤ q →
        lagrangeanObjective A b c (polyhedron D d) q ≤
          lagrangeanObjective A b c (polyhedron D d) p) ∧
      lagrangeanObjective A b c (polyhedron D d) p =
        ((c ⬝ᵥ xstar : ℝ) : EReal) := by
  sorry
