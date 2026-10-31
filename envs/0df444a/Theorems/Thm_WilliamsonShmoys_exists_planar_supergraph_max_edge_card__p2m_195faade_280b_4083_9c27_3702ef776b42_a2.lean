-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_edge_card__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
-- name    : WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:40.724369+00:00
-- url     : https://prove2.me/theorems/c1b261ba-306d-4a6e-a5c0-9da269f5f325
-- title:
--   Maximum edge count among drawable supergraphs
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
      (∀ S : SimpleGraph V, Q ≤ S → WilliamsonShmoys.HasPlanarDrawingOn S →
        S.edgeSet.ncard ≤ R.edgeSet.ncard) := by
  sorry
