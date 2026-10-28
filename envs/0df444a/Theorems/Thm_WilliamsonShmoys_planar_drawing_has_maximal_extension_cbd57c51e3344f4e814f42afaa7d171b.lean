-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:16:06.535272+00:00
-- url     : https://prove2.me/theorems/ea4a47bd-d853-41aa-bbfd-9fddc36f87ce
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite simple graph on the given vertex type has a drawable supergraph on that vertex type that is maximal by edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_cbd57c51e3344f4e814f42afaa7d171b
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = H.edgeSet := by sorry
