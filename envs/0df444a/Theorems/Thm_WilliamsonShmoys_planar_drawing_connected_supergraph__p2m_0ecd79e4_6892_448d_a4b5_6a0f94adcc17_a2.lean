-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_0ecd79e4_6892_448d_a4b5_6a0f94adcc17_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_0ecd79e4_6892_448d_a4b5_6a0f94adcc17_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T21:52:10.910676+00:00
-- url     : https://prove2.me/theorems/68eaa3da-fd91-4042-a16c-b2e1a43cfadf
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertex type, containing its edges and with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_0ecd79e4_6892_448d_a4b5_6a0f94adcc17_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    exists K : SimpleGraph V,
      J <= K /\ K.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        J.edgeSet.ncard <= K.edgeSet.ncard := by sorry
