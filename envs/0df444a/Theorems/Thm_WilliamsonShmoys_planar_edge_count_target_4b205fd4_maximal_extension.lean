-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_target_4b205fd4_maximal_extension
-- name    : WilliamsonShmoys.planar_edge_count_target_4b205fd4_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:55:59.359733+00:00
-- url     : https://prove2.me/theorems/b601611a-9331-48a6-9528-53a6702cfb31
-- title:
--   Maximal drawable extension on a fixed vertex set
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable supergraphs and has at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_target_4b205fd4_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
        (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
