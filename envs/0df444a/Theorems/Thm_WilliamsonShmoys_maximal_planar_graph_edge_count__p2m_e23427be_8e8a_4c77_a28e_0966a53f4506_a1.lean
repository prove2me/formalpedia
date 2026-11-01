-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:03.271105+00:00
-- url     : https://prove2.me/theorems/2368bce9-0700-4bbd-ab4b-7c13a596af1d
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
