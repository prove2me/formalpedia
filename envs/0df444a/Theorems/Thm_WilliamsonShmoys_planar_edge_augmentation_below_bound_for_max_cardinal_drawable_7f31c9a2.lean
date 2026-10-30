-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound_for_max_cardinal_drawable_7f31c9a2
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_bound_for_max_cardinal_drawable_7f31c9a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:59:06.087758+00:00
-- url     : https://prove2.me/theorems/72237221-a8b4-4f4d-8f83-4504f9e5ce12
-- title:
--   Drawable edge augmentation below the planar bound
-- statement:
--   If a drawable simple graph on at least three vertices has strictly fewer than three times the vertex count minus six edges, it has a drawable supergraph on the same vertex type with more edges. A proof route is to extend it to an edge-maximal drawable graph and use the triangulation edge count to rule out the extension having the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_below_bound_for_max_cardinal_drawable_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      K.edgeSet.ncard < H.edgeSet.ncard := by sorry
