-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9
-- name    : WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:34:52.451146+00:00
-- url     : https://prove2.me/theorems/d7faa0de-0310-405d-98f9-7d951a11cacf
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3|V| − 6` edges. At the boundary `|V| = 3`, maximality forces the triangle, so the equality still holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
