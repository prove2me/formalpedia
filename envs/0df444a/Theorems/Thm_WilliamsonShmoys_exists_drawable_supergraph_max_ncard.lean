-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_max_ncard
-- name    : WilliamsonShmoys.exists_drawable_supergraph_max_ncard
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:24:08.429158+00:00
-- url     : https://prove2.me/theorems/773f1160-cbe8-4622-b51f-079bb5f8f2f5
-- title:
--   A drawable supergraph with maximum edge-set cardinality exists
-- statement:
--   Among drawable supergraphs of `L`, one has an edge set with cardinality at least that of every other drawable supergraph of `L`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_drawable_supergraph_max_ncard
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, L ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
