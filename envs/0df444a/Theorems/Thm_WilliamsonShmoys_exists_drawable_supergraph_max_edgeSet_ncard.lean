-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_edgeSet_ncard
-- name    : WilliamsonShmoys.exists_drawable_supergraph_max_edgeSet_ncard
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:34:03.749667+00:00
-- url     : https://prove2.me/theorems/24006843-4eb1-4c01-bca0-e8b028858443
-- title:
--   Finite edge-count maximum among drawable supergraphs
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_drawable_supergraph_max_edgeSet_ncard
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
