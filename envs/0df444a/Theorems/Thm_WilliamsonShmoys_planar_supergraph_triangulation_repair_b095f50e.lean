-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_repair_b095f50e
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_repair_b095f50e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:50:47.053363+00:00
-- url     : https://prove2.me/theorems/0ecd3e0b-33db-4d9b-b342-36c364c700f5
-- title:
--   Triangulated drawable supergraph completion
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has a drawable supergraph on that same vertex type whose edge count plus six is three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_repair_b095f50e
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
