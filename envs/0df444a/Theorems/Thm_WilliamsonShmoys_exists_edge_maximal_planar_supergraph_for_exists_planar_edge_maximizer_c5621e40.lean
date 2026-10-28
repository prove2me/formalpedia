-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_for_exists_planar_edge_maximizer_c5621e40
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exists_planar_edge_maximizer_c5621e40
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:34:33.573503+00:00
-- url     : https://prove2.me/theorems/5d32453f-2470-4b06-b222-223bffad02af
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_for_exists_planar_edge_maximizer_c5621e40
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
