-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3_exists_maximal_supergraph
-- name    : WilliamsonShmoys.edge_count_planar_upper_retry3_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:59:26.284648+00:00
-- url     : https://prove2.me/theorems/7723ce87-cdc1-4b78-95d6-5eddc4894df9
-- title:
--   Extend a planar drawing to an edge-maximal supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal under graph inclusion and has at least as many edges. The boundary cases are included: the finite family of drawable supergraphs contains the original graph, even when it has few vertices or no edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_planar_upper_retry3_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
