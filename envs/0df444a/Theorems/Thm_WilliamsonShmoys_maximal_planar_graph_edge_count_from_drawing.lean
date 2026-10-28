-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_from_drawing
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_from_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:18:43.831713+00:00
-- url     : https://prove2.me/theorems/98aa9194-93a2-4249-a7de-462075897e3f
-- title:
--   A maximal drawable graph has the tight planar edge count
-- statement:
--   A graph maximal among drawable supergraphs on the given vertex type has exactly three times the number of vertices minus six edges, provided there are at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_from_drawing {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
