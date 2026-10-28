-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_maximal_supergraph
-- name    : WilliamsonShmoys.exists_drawable_edge_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:49:41.960599+00:00
-- url     : https://prove2.me/theorems/3bed8913-eb61-4d1a-9bd7-4a5cdd37c0f2
-- title:
--   An edge-maximal drawable supergraph exists
-- statement:
--   For a finite ordered vertex type, every drawable graph is contained in a drawable graph that is maximal among drawable supergraphs on that same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_drawable_edge_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by
  sorry
