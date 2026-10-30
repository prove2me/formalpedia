-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_fixed_vertex_0e6cbe52_e2e3_41cf_80dc_2d34dacc7938
-- name    : WilliamsonShmoys.planar_triangulation_extension_fixed_vertex_0e6cbe52_e2e3_41cf_80dc_2d34dacc7938
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:21:22.989369+00:00
-- url     : https://prove2.me/theorems/c27addfb-131a-4167-b7de-c130c93bb2da
-- title:
--   Planar triangulation extension on a fixed vertex set
-- statement:
--   Every drawable simple graph on a finite ordered vertex set with at least three vertices is a subgraph of a drawable triangulation on the same vertices, with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_fixed_vertex_0e6cbe52_e2e3_41cf_80dc_2d34dacc7938
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  sorry
