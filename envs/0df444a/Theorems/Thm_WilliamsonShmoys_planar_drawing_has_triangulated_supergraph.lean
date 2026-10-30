-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:05:17.159312+00:00
-- url     : https://prove2.me/theorems/966525e1-3468-461a-9efb-2057e1826c85
-- title:
--   Triangulated planar supergraph
-- statement:
--   Any finite planar drawing on at least three vertices can be extended, using the same vertex set, to a planar graph with exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
