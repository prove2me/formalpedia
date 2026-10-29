-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:20:25.721994+00:00
-- url     : https://prove2.me/theorems/7e088558-29fd-4fbd-a7a0-13310434332d
-- title:
--   Triangulation extension for the planar edge bound
-- statement:
--   Every drawable simple graph on a fixed finite ordered vertex set of size at least three extends to a drawable supergraph on that same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
