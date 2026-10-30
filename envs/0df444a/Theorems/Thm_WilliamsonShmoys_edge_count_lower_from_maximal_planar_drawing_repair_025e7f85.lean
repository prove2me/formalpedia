-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_lower_from_maximal_planar_drawing_repair_025e7f85
-- name    : WilliamsonShmoys.edge_count_lower_from_maximal_planar_drawing_repair_025e7f85
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:34:25.081833+00:00
-- url     : https://prove2.me/theorems/b7122715-0728-4437-959c-fa9b221855f8
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A finite simple graph with at least three vertices that is maximal among drawable graphs on the same vertex type has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_lower_from_maximal_planar_drawing_repair_025e7f85 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
