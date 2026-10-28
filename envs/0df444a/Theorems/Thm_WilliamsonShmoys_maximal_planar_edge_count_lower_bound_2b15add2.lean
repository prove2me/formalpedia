-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_2b15add2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_2b15add2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:47:00.128973+00:00
-- url     : https://prove2.me/theorems/eaf18453-92a5-4ca5-8576-324d89e6d6b8
-- title:
--   Lower bound from maximality and triangulation
-- statement:
--   An inclusion-maximal graph with the specified crossing-free drawing and at least three vertices has at least three times its vertex count minus six edges. This is the maximality-to-triangulation step: augment the drawing to a triangulation using the same vertices, apply `hmax` to the augmented graph, and count edges by Euler’s formula. The case of exactly three vertices is the triangle case. This removes the lower-bound and augmentation argument from the parent; a concrete proof route still needs a formal planar augmentation argument compatible with `HasPlanarDrawingOn`. That topological augmentation argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_2b15add2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = L) : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
