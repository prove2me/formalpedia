-- Prove2me | Theorems.Thm_Hirsch_diamLE_of_vertex_listing
-- name    : Hirsch.diamLE_of_vertex_listing
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T08:26:27.543096+00:00
-- url     : https://prove2.me/theorems/0d0973c0-0c5b-444a-840f-fac6cf7e326d
-- title:
--   Vertex listing bounds padded graph diameter by $m-1$
-- statement:
--   Let $P\subseteq\mathbb R^d$ be an H-polyhedron cut out by $n$ linear inequalities, and suppose its vertices (extreme points) can be listed in $m$ slots, allowing duplicates. Then the padded vertex-edge diameter of $P$ is at most $m-1$:
--
--   $$
--   \operatorname{DiamLE}(P,\, m-1).
--   $$
--
--   In particular, if $P$ has $v$ vertices then $\operatorname{DiamLE}(P, v-1)$. Boundedness is not assumed: the platform connectivity theorem already supplies some finite walk between any two vertices of an arbitrary H-polyhedron, and a shortest such walk cannot repeat a vertex, so its length is at most one less than the number of distinct vertices.
--
--   This is the classical trivial bound $\operatorname{diam}(G)\le |V(G)|-1$ for a connected graph, applied to the $1$-skeleton. It does not produce a uniform polynomial in $n+d$, because a $d$-polytope may have exponentially many vertices.
--
--   **Formalization Note** The listing is a map `Fin m → EuclideanSpace ℝ (Fin d)` that hits every extreme point. If $m=0$ and there are no extreme points the claim is vacuous; if extreme points exist then $m\ge 1$. Stationary padding makes the predicate monotone in the budget.
-- source:
--   Classical bound diam(G) ≤ |V(G)|−1 for a connected graph, applied to the 1-skeleton of an H-polyhedron. Connectivity is Hirsch.graph_connected_general on Prove2Me (theorem 8b17b820-f7a3-42e4-89a3-efd89fad4f3b). See also Ziegler, Lectures on Polytopes, Lecture 3 (graph of a polytope is connected); Grünbaum, Convex Polytopes, Chapter 3.

import Definitions.Def_Hirsch_model
set_option autoImplicit false
open Set Hirsch

namespace Hirsch

theorem diamLE_of_vertex_listing {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (vertices : Fin m → EuclideanSpace ℝ (Fin d))
    (hcover : ∀ x ∈ extremePoints ℝ (Hpoly a b), ∃ j, vertices j = x) :
    DiamLE (Hpoly a b) (m - 1) := by sorry

end Hirsch
