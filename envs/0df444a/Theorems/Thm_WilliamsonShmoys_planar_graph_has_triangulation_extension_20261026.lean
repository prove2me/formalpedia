-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_extension_20261026
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_extension_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:04:48.58938+00:00
-- url     : https://prove2.me/theorems/a20098b3-c6c6-4131-9242-d5e3678d726d
-- title:
--   Triangulation completion of a finite planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertex type with exactly three times the number of vertices minus six edges. This is the triangulation-completion step: add noncrossing edges until the embedding is maximal, then use Euler’s formula and the fact that each face is triangular. The boundary case of three vertices gives the complete graph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_triangulation_extension_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
