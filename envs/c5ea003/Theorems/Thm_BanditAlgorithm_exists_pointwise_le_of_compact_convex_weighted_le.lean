-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_pointwise_le_of_compact_convex_weighted_le
-- name    : BanditAlgorithm.exists_pointwise_le_of_compact_convex_weighted_le
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T18:17:22.666803+00:00
-- url     : https://prove2.me/theorems/fd296e2b-433a-4fc1-8fd1-73f9d5269cd0
-- title:
--   Finite Sion minimax: weighted bounds imply one pointwise bound
-- statement:
--   Let $X$ be a nonempty compact convex subset of a real normed space and let $g:X\to\mathbb R^I$ be the restriction of a continuous linear map, where $I$ is finite and nonempty. If for every probability vector $\lambda$ on $I$ there is an $x\in X$ with\n\n$$\sum_{i\in I}\lambda_i g(x)_i\le C,$$\n\nthen there is a single $x\in X$ such that $g(x)_i\le C$ for every $i\in I$.\n\nThe proof applies Sion’s minimax theorem to the bilinear payoff $(x,\lambda)\mapsto\sum_i\lambda_i g(x)_i$ and evaluates the resulting saddle point at each simplex vertex.\n\n**Formalization Note** This is the exact finite-outcome minimax interface used to pass from the mixed-outcome water-transfer construction to simultaneous one-step bounds.
-- source:
--   Maurice Sion, On general minimax theorems, Pacific Journal of Mathematics 8 (1958), 171–176; applied as in Lattimore and Szepesvári, Bandit Algorithms (2020), Eq. (37.16), printed p. 499. https://tor-lattimore.com/downloads/book/book.pdf

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

theorem BanditAlgorithm.exists_pointwise_le_of_compact_convex_weighted_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] [Nonempty I]
    (X : Set E) (hXne : X.Nonempty) (hXconv : Convex ℝ X) (hXcomp : IsCompact X)
    (g : E →L[ℝ] (I → ℝ)) (C : ℝ)
    (hweighted : ∀ lam : I → ℝ, lam ∈ stdSimplex ℝ I →
      ∃ x ∈ X, ∑ i : I, lam i * g x i ≤ C) :
    ∃ x ∈ X, ∀ i : I, g x i ≤ C := by sorry
