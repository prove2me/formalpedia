-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_via_triangulation_589bf4c0
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_via_triangulation_589bf4c0
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:53:23.112619+00:00
-- url     : https://prove2.me/theorems/0dd02aa4-d82b-4c99-8dc9-30c32e3afc6d
-- title:
--   Maximal drawable graphs reach the planar edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_via_triangulation_589bf4c0
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
