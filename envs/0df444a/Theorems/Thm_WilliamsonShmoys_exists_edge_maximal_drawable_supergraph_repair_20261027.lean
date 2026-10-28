-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_drawable_supergraph_repair_20261027
-- name    : WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_repair_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:13:42.148761+00:00
-- url     : https://prove2.me/theorems/e3f3982a-e294-4fcd-b213-caa989637012
-- title:
--   Maximum-edge drawable supergraph
-- statement:
--   Among drawable supergraphs of W on the finite vertex type V, one has maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_drawable_supergraph_repair_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ H : SimpleGraph V, W ≤ H →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H.edgeSet.ncard ≤ U.edgeSet.ncard := by sorry
