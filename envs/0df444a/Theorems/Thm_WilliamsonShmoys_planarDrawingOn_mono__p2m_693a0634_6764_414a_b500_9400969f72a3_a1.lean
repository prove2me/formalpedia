-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
-- name    : WilliamsonShmoys.planarDrawingOn_mono__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:39.047984+00:00
-- url     : https://prove2.me/theorems/202d3bce-981e-4819-a435-2866353fbab1
-- title:
--   Planar drawing is preserved by edge restriction
-- statement:
--   If every edge of G is an edge of H and H has a planar drawing on V, then G has a planar drawing on V.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_mono__p2m_693a0634_6764_414a_b500_9400969f72a3_a1 {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hGH : G.edgeSet ⊆ H.edgeSet) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
