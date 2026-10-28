-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_reaches_triangulation_bound_from_arc_drawing
-- name    : WilliamsonShmoys.planar_supergraph_reaches_triangulation_bound_from_arc_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:32:42.510996+00:00
-- url     : https://prove2.me/theorems/66ba9c1f-cf00-4c5b-ab7d-b77104994fe7
-- title:
--   Augment an arc-drawn planar graph to the triangulation bound
-- statement:
--   For a drawable graph on a fixed finite vertex set of size at least three, there is a drawable supergraph on that same set with at least 3|V|−6 edges. The boundary case of three vertices permits the triangle. A proof route is to maximize the edge count among drawable supergraphs, show that any nontriangular face allows a missing edge to be inserted within that face, then apply Euler’s formula. The face and edge-insertion arguments for the supplied arc-based drawing predicate are the main remaining work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_reaches_triangulation_bound_from_arc_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 <= M.edgeSet.ncard := by
  sorry
