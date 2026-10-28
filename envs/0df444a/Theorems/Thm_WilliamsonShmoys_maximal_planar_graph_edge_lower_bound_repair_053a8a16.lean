-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound_repair_053a8a16
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_repair_053a8a16
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:17:24.208207+00:00
-- url     : https://prove2.me/theorems/a314ea99-c3f8-4d7b-bf02-297b18db378b
-- title:
--   A maximal drawable graph has at least 3n − 6 edges
-- statement:
--   A drawable simple graph maximal under drawable edge-set extensions on the same vertex type has at least 3n − 6 edges. A proof route is to show maximality rules out any face with a boundary that admits an added diagonal, deduce triangular faces, and apply Euler’s formula. The topology of this step is the main remaining obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_repair_053a8a16
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ W : SimpleGraph V,
      G.edgeSet ⊆ W.edgeSet →
      HasPlanarDrawingOn W →
      W.edgeSet ⊆ G.edgeSet) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
