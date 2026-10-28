-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq_euler
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:30:12.474005+00:00
-- url     : https://prove2.me/theorems/2d86ab74-e95f-4be3-b60e-f9414e86f17b
-- title:
--   Exact edge count of a maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has exactly 3n − 6 edges. This isolates the triangulation and Euler step needed by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq_euler {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
