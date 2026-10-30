-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_fixed_vertices_5000a3d3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices_5000a3d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:59:15.678387+00:00
-- url     : https://prove2.me/theorems/e7f6fb70-4e9a-4f92-95c8-3dceeaed3f7f
-- title:
--   An inclusion-maximal planar graph has 3n minus 6 edges
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices_5000a3d3
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V,
      X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y ≤ X) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
