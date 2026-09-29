-- Prove2me | Theorems.Thm_Hirsch_polynomial_hirsch_conjecture
-- name    : Hirsch.polynomial_hirsch_conjecture
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-08-22T02:25:36.75778+00:00
-- url     : https://prove2.me/theorems/58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac
-- title:
--   The polynomial Hirsch conjecture
-- statement:
--   **The polynomial Hirsch conjecture.** There exist constants $c, k \in \mathbb{N}$ such that every nonempty bounded H-polytope $P = \{x \in \mathbb{R}^d \mid \langle a_i, x\rangle \le b_i,\ i \le n\}$ has combinatorial diameter at most $c\,(n+d)^k$: every two vertices are joined by a path of at most $c\,(n+d)^k$ edges.
--
--   Every polynomial in $n$ and $d$ is dominated by some $c(n+d)^k$ and conversely, so the statement is exactly "the diameter of a polytope is polynomially bounded in its dimension and number of defining inequalities". The original Hirsch conjecture ($n - d$) was disproved by Santos (2012); all known counterexamples violate the bound by a constant factor, while the best proven upper bounds (Kalai--Kleitman 1992, Todd 2014) are quasi-polynomial, $n^{O(\log d)}$. A positive answer is necessary for any pivot rule of the simplex method to be worst-case polynomial; the question was the subject of the Polymath 3 project.
-- source:
--   Kalai, The polynomial Hirsch conjecture (Polymath 3), 2010, https://gilkalai.wordpress.com/2010/09/29/the-polynomial-hirsch-conjecture-a-proposal-for-polymath3/; survey: Santos, TOP 21 (2013), https://arxiv.org/abs/1307.5900

import Mathlib
import Definitions.Def_Hirsch_model

namespace Hirsch

theorem polynomial_hirsch_conjecture :
    ∃ c k : ℕ, ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (c * (n + d) ^ k) := by sorry

end Hirsch
