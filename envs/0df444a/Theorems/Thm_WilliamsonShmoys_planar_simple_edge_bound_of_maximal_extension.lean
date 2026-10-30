-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_of_maximal_extension
-- name    : WilliamsonShmoys.planar_simple_edge_bound_of_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:32:04.607703+00:00
-- url     : https://prove2.me/theorems/4712be9d-2fc8-4fef-ae62-13ce01d367b6
-- title:
--   Edge bound for a maximal planar graph
-- statement:
--   An inclusion-maximal finite simple planar graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound_of_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
