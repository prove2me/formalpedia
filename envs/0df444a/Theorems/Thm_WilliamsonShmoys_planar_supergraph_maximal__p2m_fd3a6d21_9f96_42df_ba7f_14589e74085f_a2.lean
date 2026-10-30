-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:00:26.76404+00:00
-- url     : https://prove2.me/theorems/768c520d-0a53-42aa-bcb6-e73e3939ed8f
-- title:
--   Extend a drawable graph to an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H →
        Set.Subset K.edgeSet H.edgeSet →
        Set.Subset H.edgeSet K.edgeSet) := by sorry
