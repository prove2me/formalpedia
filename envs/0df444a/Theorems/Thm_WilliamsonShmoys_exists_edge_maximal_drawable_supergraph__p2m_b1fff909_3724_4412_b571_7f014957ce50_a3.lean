-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
-- name    : WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:12:47.113041+00:00
-- url     : https://prove2.me/theorems/eef664be-1603-4195-b44b-d81e1ccffc6c
-- title:
--   A drawable graph has an edge-maximal drawable supergraph
-- statement:
--   Among the finitely many drawable supergraphs of J on V, choose one with greatest edge count. This removes the existence of a maximal extension from the parent; prove it by finite maximization, using J itself to show the candidate set is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_drawable_supergraph__p2m_b1fff909_3724_4412_b571_7f014957ce50_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
