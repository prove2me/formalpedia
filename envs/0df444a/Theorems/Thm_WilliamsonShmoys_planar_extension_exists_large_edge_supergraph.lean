-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_exists_large_edge_supergraph
-- name    : WilliamsonShmoys.planar_extension_exists_large_edge_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:43:11.495095+00:00
-- url     : https://prove2.me/theorems/feafdeb8-087e-46ef-8af7-a56169435f6d
-- title:
--   Drawable supergraph with the planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_exists_large_edge_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ Z : SimpleGraph V, G ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      3 * Fintype.card V ≤ Z.edgeSet.ncard + 6 := by sorry
