-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_e696380b
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e696380b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:48:21.022271+00:00
-- url     : https://prove2.me/theorems/044cb63f-2de3-48f9-8f63-130b57b1bde5
-- title:
--   Drawable maximal supergraph on the same vertices
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e696380b
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ H : SimpleGraph V,
          K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = K := by sorry
