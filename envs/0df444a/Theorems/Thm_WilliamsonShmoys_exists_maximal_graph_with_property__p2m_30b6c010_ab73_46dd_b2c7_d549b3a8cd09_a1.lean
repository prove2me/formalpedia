-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_graph_with_property__p2m_30b6c010_ab73_46dd_b2c7_d549b3a8cd09_a1
-- name    : WilliamsonShmoys.exists_maximal_graph_with_property__p2m_30b6c010_ab73_46dd_b2c7_d549b3a8cd09_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:22:07.504529+00:00
-- url     : https://prove2.me/theorems/c908f095-92e1-4932-9921-16f641cd7b7a
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property of graphs on a finite linearly ordered vertex type, every graph satisfying the property is contained in a property-satisfying graph maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_graph_with_property__p2m_30b6c010_ab73_46dd_b2c7_d549b3a8cd09_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ T : SimpleGraph V,
      G.edgeSet ⊆ T.edgeSet ∧
        P T ∧
          ∀ H : SimpleGraph V,
            T.edgeSet ⊆ H.edgeSet → P H → H.edgeSet ⊆ T.edgeSet := by
  sorry
