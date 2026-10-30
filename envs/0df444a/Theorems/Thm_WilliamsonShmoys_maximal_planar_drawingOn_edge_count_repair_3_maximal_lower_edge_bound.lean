-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_repair_3_maximal_lower_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3_maximal_lower_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:01:04.507157+00:00
-- url     : https://prove2.me/theorems/3866b437-4938-4cb4-96fc-954e96126455
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   If a drawable graph on at least three vertices is inclusion maximal among drawable supergraphs on the same vertex type, it has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3_maximal_lower_edge_bound {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N ∧ (∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H → N.edgeSet ⊆ H.edgeSet → H.edgeSet ⊆ N.edgeSet)) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
