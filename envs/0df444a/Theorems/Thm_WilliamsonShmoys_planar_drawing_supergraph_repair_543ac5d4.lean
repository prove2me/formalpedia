-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_repair_543ac5d4
-- name    : WilliamsonShmoys.planar_drawing_supergraph_repair_543ac5d4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:20:03.737505+00:00
-- url     : https://prove2.me/theorems/0eea4e02-f00f-4c62-a653-3f4212d03bee
-- title:
--   Maximum-edge drawable supergraph exists
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_repair_543ac5d4
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S <= T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T <= U → WilliamsonShmoys.HasPlanarDrawingOn U →
          U.edgeSet.ncard ≤ T.edgeSet.ncard := by sorry
