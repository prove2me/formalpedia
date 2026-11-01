-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:22:15.427336+00:00
-- url     : https://prove2.me/theorems/aca45187-d3cf-47bf-b721-87db9751a89d
-- title:
--   Planar drawing is preserved by deleting edges
-- statement:
--   If H's edge set is contained in G's and G has a planar drawing, then H has a planar drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_a584cd68_9d17_4361_8b29_312b20e50fca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hsub : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
