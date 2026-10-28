-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_from_drawing
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph_from_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:02:30.941823+00:00
-- url     : https://prove2.me/theorems/1e48beb1-4ed1-4698-a935-7247c5c465c3
-- title:
--   Every finite planar graph extends to a triangulation
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing on those vertices is contained in a graph on the same vertex set that has a crossing-free drawing and exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
