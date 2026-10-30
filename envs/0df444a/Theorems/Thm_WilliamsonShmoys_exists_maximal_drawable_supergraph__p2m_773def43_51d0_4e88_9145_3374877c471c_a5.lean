-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:44:06.845984+00:00
-- url     : https://prove2.me/theorems/3abbe82f-77ba-4e7e-998b-8a5cd1cda5aa
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal under inclusion. Choose a graph with maximum edge count among the finitely many drawable supergraphs of the original graph; any drawable strict supergraph would contradict that choice. This removes the finite maximal-extension step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
