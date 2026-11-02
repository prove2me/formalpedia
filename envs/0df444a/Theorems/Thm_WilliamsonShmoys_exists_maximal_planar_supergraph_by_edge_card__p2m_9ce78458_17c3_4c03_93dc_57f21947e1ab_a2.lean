-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_by_edge_card__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_by_edge_card__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:55.073103+00:00
-- url     : https://prove2.me/theorems/7124e163-71d0-42f5-b2b2-020594fd6b9a
-- title:
--   A drawable extension with maximum edge count
-- statement:
--   Among drawable supergraphs of a given drawable graph on a finite ordered vertex type, one has at least as many edges as every other drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_by_edge_card__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        Set.ncard H.edgeSet ≥ Set.ncard K.edgeSet := by sorry
