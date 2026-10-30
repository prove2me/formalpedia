-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v3
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:51:22.519907+00:00
-- url     : https://prove2.me/theorems/48deed52-c722-4185-acf2-8da11ea6caf7
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : ∀ Z : SimpleGraph V,
      LE.le Y Z →
      WilliamsonShmoys.HasPlanarDrawingOn Z →
      Z = Y)
    (hV : 3 <= Fintype.card V) :
    Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
