-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_395ae7cf
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_count_395ae7cf
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:37:19.577387+00:00
-- url     : https://prove2.me/theorems/213a5b3a-6bcf-47f8-a9fb-eeb482e02cde
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An inclusion-maximal simple planar graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_count_395ae7cf
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ J : SimpleGraph V, G ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
