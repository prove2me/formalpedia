-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_triangulation_extension
-- name    : WilliamsonShmoys.planar_edge_count_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:19:36.469979+00:00
-- url     : https://prove2.me/theorems/fe58c870-e3e9-466f-b8e7-756f412ad0cc
-- title:
--   Extend a connected planar drawing to a maximal planar graph
-- statement:
--   Every connected finite simple graph on at least three vertices with a crossing-free drawing has a planar supergraph on the same vertices whose edge count is exactly 3|V|−6. The extension must handle bridges and trees, not assume the original drawing already has triangular face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
