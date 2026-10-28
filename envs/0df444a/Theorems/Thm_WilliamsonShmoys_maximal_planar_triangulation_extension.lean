-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:40:17.15923+00:00
-- url     : https://prove2.me/theorems/279755a6-02cd-4483-9b65-417cbe6cd492
-- title:
--   Every drawable graph extends to a triangulation
-- statement:
--   Every crossing-free drawable graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertex type whose edge count is `3 * |V| - 6`. This isolates the planar triangulation-extension construction. It preserves the size and drawing hypotheses, and covers disconnected graphs and isolated vertices; at three vertices the extension can be the triangle. A proof can extend the supplied plane drawing by adding noncrossing edges until it is maximal, then derive the count from Euler's formula and triangular faces. The construction from the exact arc predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
