-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:23:30.587004+00:00
-- url     : https://prove2.me/theorems/28ec584f-06dd-4d16-a27c-0763052ee42f
-- title:
--   Edge lower bound for an edge-maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable supergraphs on the same vertex set has at least 3|V|−6 edges. This removes the planar edge-count step from the parent. A proof route is to use maximality to establish connectedness and triangular faces for the plane embedding, then apply Euler’s formula and identify the graph’s edge count with `edgeSet.ncard`. When |V| = 3, maximality gives the triangle and equality in the bound. The remaining core obligation is formalizing these embedding and Euler arguments for the supplied drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
