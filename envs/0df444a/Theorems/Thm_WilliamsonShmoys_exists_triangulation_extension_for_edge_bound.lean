-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulation_extension_for_edge_bound
-- name    : WilliamsonShmoys.exists_triangulation_extension_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:37:37.094383+00:00
-- url     : https://prove2.me/theorems/f74d028f-14cb-480b-9e7a-969a774553c9
-- title:
--   Extend a planar drawing to a triangulation for the edge bound
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing extends, on the same vertex type, to a crossing-free simple graph with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulation_extension_for_edge_bound {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
