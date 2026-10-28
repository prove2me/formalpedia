-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_completion
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:10:30.56364+00:00
-- url     : https://prove2.me/theorems/68f3de31-6cd8-4ab3-a74f-3c10a31cd1ba
-- title:
--   Every connected planar graph has a triangulated completion on the same vertices
-- statement:
--   Any connected graph with at least three vertices that has a planar drawing can be extended, without adding vertices, to a planar supergraph with triangular face data satisfying the edge-incidence and Euler conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.planar_graph_has_triangulated_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists H' : SimpleGraph V,
      H <= H' ∧
      WilliamsonShmoys.HasPlanarDrawingOn H' ∧
      WilliamsonShmoys.HasTriangularPlaneFaceSystem H' := by sorry
