-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T18:21:55.106246+00:00
-- url     : https://prove2.me/theorems/4f2e8e58-9c90-44c4-8654-a4daa39e2192
-- title:
--   Connecting components of a planar drawing
-- statement:
--   Every finite graph with the supplied crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing and at least as many edges. The drawing predicate requires distinct vertex points, injective continuous edge arcs, no edge interiors through vertices, and intersections between distinct edges only at shared endpoints. The geometric construction joins drawing components through the complement of the existing finite drawing; it preserves the original arcs and adds only edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun G : SimpleGraph V =>
      H <= G /\ G.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn G /\
      H.edgeSet.ncard <= G.edgeSet.ncard := by
  sorry
