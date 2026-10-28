-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_edge_count
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:36:18.440662+00:00
-- url     : https://prove2.me/theorems/7845ca9a-2491-471f-bf00-56c89f02f99c
-- title:
--   Planar drawing extends to a triangulation supergraph with the maximal edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V| − 6 edges. Extend the drawing to a triangulation and count its edges using Euler’s formula. This child supplies the geometric extension and counting step; the parent derives the target from maximality and equality of the supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists M : SimpleGraph V, N <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
