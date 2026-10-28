-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension_5685a8d2
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension_5685a8d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:32:48.900911+00:00
-- url     : https://prove2.me/theorems/0d017e56-dde5-43e5-a3ee-39f25d675775
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. The result includes empty and small vertex types; it does not claim a particular edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_extension_5685a8d2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet ∧
      HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V,
        G.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K →
        K.edgeSet = G.edgeSet := by sorry
