-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_exists_edge_maximal_planar_supergraph
-- name    : WilliamsonShmoys.triangulation_exists_edge_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:55:21.455989+00:00
-- url     : https://prove2.me/theorems/67ff4b98-9163-4da2-9b8f-f47ccaee5a3c
-- title:
--   Existence of an edge-maximal drawable supergraph for triangulation
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set whose edge count is at least that of the original and maximal among drawable supergraphs containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.triangulation_exists_edge_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T.edgeSet.ncard ≤ U.edgeSet.ncard ∧
      (∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W →
        W.edgeSet.ncard ≤ U.edgeSet.ncard) := by sorry
