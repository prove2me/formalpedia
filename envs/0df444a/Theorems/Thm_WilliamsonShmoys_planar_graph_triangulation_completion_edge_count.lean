-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion_edge_count
-- name    : WilliamsonShmoys.planar_graph_triangulation_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:17:41.540682+00:00
-- url     : https://prove2.me/theorems/d8e86b30-fed1-4ee5-9c6d-8ff76555c4e7
-- title:
--   Planar graph completion to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable graph on the same vertex type whose edge count is exactly `3n − 6`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      3 * Fintype.card V = R.edgeSet.ncard + 6 := by sorry
