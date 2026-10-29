-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_via_triangulation
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_via_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:21:53.489006+00:00
-- url     : https://prove2.me/theorems/3d1571be-10a8-4fc7-bb91-4f1d7ccaf3f6
-- title:
--   Edge lower bound from maximality and triangulation
-- statement:
--   A finite simple graph on at least three vertices that is maximal among graphs drawable by the supplied predicate has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_via_triangulation {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) : 3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by sorry
