-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_augmentation_for_euler_bound_edge_count
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:31:26.320048+00:00
-- url     : https://prove2.me/theorems/6371ac88-6bee-4ed8-a9a6-c374e5df5035
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is inclusion-maximal among drawable supergraphs on that vertex type has exactly 3|V|−6 edges. The proof route is to establish connectedness and triangular faces for a maximal plane drawing, then count face-edge incidences using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_augmentation_for_euler_bound_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
