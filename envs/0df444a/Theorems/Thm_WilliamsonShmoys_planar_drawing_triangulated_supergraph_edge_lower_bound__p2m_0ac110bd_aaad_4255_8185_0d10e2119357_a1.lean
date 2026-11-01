-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_supergraph_edge_lower_bound__p2m_0ac110bd_aaad_4255_8185_0d10e2119357_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_lower_bound__p2m_0ac110bd_aaad_4255_8185_0d10e2119357_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:28.96582+00:00
-- url     : https://prove2.me/theorems/150f7ba2-65b7-4a49-8255-d3333730e062
-- title:
--   Planar drawing triangulated supergraph edge lower bound
-- statement:
--   Every crossing-free drawing of a finite simple graph on at least three vertices extends, on the same vertex type, to a planar supergraph with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_lower_bound__p2m_0ac110bd_aaad_4255_8185_0d10e2119357_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
