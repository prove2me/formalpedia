-- Prove2me | Theorems.Thm_Hirsch_zero_one_polytope_diameter_le_dimension
-- name    : Hirsch.zero_one_polytope_diameter_le_dimension
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T05:51:50.611108+00:00
-- url     : https://prove2.me/theorems/c3e6e689-f89a-4644-9388-97b9983d141e
-- title:
--   Naddef: a $0/1$ polytope has graph diameter at most its dimension
-- statement:
--   **Naddef's theorem for $0/1$ H-polytopes.** Let $P=\{x\in\mathbb{R}^d:\langle a_i,x\rangle\le b_i,\ i\le n\}$ be a nonempty bounded H-polytope whose extreme points all have coordinates in $\{0,1\}$. Then the vertex-edge graph of $P$ has combinatorial diameter at most $d$: any two vertices are joined by a padded walk of at most $d$ edges.
--
--   The argument is Naddef's induction on the number of coordinates that actually vary among vertices. The convex hull of the $0/1$ vertices lies in the unit cube, so each coordinate slice $P\cap\{x_j=\alpha\}$ with $\alpha\in\{0,1\}$ is a face. If two vertices share a varying coordinate they lie on such a face, whose varying-coordinate count is strictly smaller. If they differ on every varying coordinate, Larman's bound is used only to produce some incident edge; the other endpoint of that edge necessarily shares a varying coordinate with the source, and the same face restriction applies. Padding then lifts the inductive walk to length $d$.
--
--   This is a restricted-family theorem (vertices in the unit cube), not a uniform polynomial bound for arbitrary H-polytopes, and it does not close the unrestricted polynomial Hirsch leaf. It does give a linear bound in the ambient dimension for every $0/1$ polytope, which is the classical Naddef form $\mathrm{diam}(P)\le d$ (and hence $\le n-d$ whenever $n\ge 2d$).
-- source:
--   Naddef, The Hirsch conjecture is true for (0,1)-polytopes, Mathematical Programming 45 (1989), 21–26, https://doi.org/10.1007/BF01589099; Ziegler, Lectures on 0/1-polytopes, arXiv:math/9909177, Theorem 29.

import Mathlib
import Definitions.Def_Hirsch_model
set_option autoImplicit false
open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem zero_one_polytope_diameter_le_dimension
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ i : Fin d, x i = 0 ∨ x i = 1) :
    DiamLE (Hpoly a b) d := by sorry

end Hirsch
