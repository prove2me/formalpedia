-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_repair_3
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:51:06.559421+00:00
-- url     : https://prove2.me/theorems/bf72528c-2cfb-4847-b4cc-dd87228e8fa8
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times its number of vertices minus six edges. This isolates the triangulation and Euler-counting step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N ∧ (∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H → N.edgeSet ⊆ H.edgeSet → H.edgeSet ⊆ N.edgeSet)) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
