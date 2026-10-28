-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_maximal_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:51:37.402753+00:00
-- url     : https://prove2.me/theorems/509700b5-7005-4e02-8d3a-84934cf00353
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges. The proof route is to derive a planar embedding from the given arcs, show maximality makes its faces triangular, and count with Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_maximal_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) (hMaximal : ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K = H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
