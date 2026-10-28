-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connectedification_retry2
-- name    : WilliamsonShmoys.planar_drawing_connectedification_retry2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T21:14:41.294921+00:00
-- url     : https://prove2.me/theorems/84b40ed8-b7d6-48f1-abcc-eaa4f668df4b
-- title:
--   Connectedify a finite planar drawing without losing edges
-- statement:
--   A finite graph with the supplied planar drawing has a connected planar simple supergraph on the same vertices whose edge count is at least as large.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connectedification_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
