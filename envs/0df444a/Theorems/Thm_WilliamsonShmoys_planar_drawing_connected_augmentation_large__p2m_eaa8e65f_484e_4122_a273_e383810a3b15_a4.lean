-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_large__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a4
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_large__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T23:31:37.040062+00:00
-- url     : https://prove2.me/theorems/b4da62c7-fe59-4a5b-a624-1469ea9ca4aa
-- title:
--   Connected augmentation of a planar drawing with at least three vertices
-- statement:
--   A drawable graph on at least three vertices can be extended, on the same vertex set, to a connected drawable graph without losing any edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_large__p2m_eaa8e65f_484e_4122_a273_e383810a3b15_a4
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    Exists fun G : SimpleGraph V =>
      H <= G ∧ G.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
        H.edgeSet.ncard <= G.edgeSet.ncard := by sorry
