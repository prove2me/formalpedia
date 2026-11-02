-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_with_exact_edge_count__p2m_b7da0b5c_b8e2_42e5_8f2d_d77c61d3fb07_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph_with_exact_edge_count__p2m_b7da0b5c_b8e2_42e5_8f2d_d77c61d3fb07_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:09:56.775196+00:00
-- url     : https://prove2.me/theorems/86ac92fe-a077-498c-8a86-bf0c24de864c
-- title:
--   Every finite planar drawing extends to a triangulated graph with the maximal planar edge count
-- statement:
--   Any graph with the specified planar drawing on at least three vertices has a planar supergraph on the same vertex set whose edge count is 3n−6. The child captures triangulation completion and its Euler count; the parent uses inclusion-maximality to show that this supergraph must equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph_with_exact_edge_count__p2m_b7da0b5c_b8e2_42e5_8f2d_d77c61d3fb07_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V,
      G ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
         3 * Fintype.card V = Q.edgeFinset.card + 6) := by sorry
