-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_3fe8be02_4541_4d0a_bbf4_850e46d722fe
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_extension_3fe8be02_4541_4d0a_bbf4_850e46d722fe
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:41:02.115433+00:00
-- url     : https://prove2.me/theorems/dabb2cbe-7fe3-4213-96ba-204afbbd922b
-- title:
--   Drawable graph extends to a triangulated planar graph
-- statement:
--   For a drawable simple graph on a finite linearly ordered vertex type with at least three vertices, there is a drawable supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_extension_3fe8be02_4541_4d0a_bbf4_850e46d722fe
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      3 * Fintype.card V = Y.edgeSet.ncard + 6 := by sorry
