-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_lower_bound_of_maximal_planar_drawing_via_threshold_euler
-- name    : WilliamsonShmoys.edge_count_lower_bound_of_maximal_planar_drawing_via_threshold_euler
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:11:32.33798+00:00
-- url     : https://prove2.me/theorems/bb20dc02-6c3e-49d4-81ba-d2e5dd682396
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_lower_bound_of_maximal_planar_drawing_via_threshold_euler {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) : 3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
