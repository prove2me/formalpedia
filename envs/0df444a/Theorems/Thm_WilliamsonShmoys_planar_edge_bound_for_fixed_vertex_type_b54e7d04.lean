-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_fixed_vertex_type_b54e7d04
-- name    : WilliamsonShmoys.planar_edge_bound_for_fixed_vertex_type_b54e7d04
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:36:01.08263+00:00
-- url     : https://prove2.me/theorems/9128c05b-8534-45c9-8b00-eb70e128ed3f
-- title:
--   Planar simple graph edge bound on a fixed vertex type
-- statement:
--   A graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most `3n − 6` edges. The size condition is needed for this bound; the proof must account for disconnected graphs and small components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_for_fixed_vertex_type_b54e7d04
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
