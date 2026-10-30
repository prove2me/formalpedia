-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_triangulation_extension_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_triangulation_extension_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:14:42.073498+00:00
-- url     : https://prove2.me/theorems/f2da4cfd-e819-4288-8676-db748164e3f1
-- title:
--   Extend a planar drawing to a maximal planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is contained in a crossing-free simple graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_triangulation_extension_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ G : SimpleGraph V,
      M.edgeSet ⊆ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
