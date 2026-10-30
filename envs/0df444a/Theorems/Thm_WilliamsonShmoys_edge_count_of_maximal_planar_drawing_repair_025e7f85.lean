-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_repair_025e7f85
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_025e7f85
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:04:08.63699+00:00
-- url     : https://prove2.me/theorems/0b8e1dde-2bec-4559-8bb8-38cbef48345d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that is inclusion-maximal among drawable graphs has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_repair_025e7f85 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
