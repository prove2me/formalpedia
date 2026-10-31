-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_6fae641e_69bd_437f_8912_51466427af04_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:40.78432+00:00
-- url     : https://prove2.me/theorems/3d35640d-f78d-47f5-a2d5-6e5c206bbbf4
-- title:
--   Connected augmentation of a planar drawing
-- statement:
--   Any finite graph with the supplied crossing-free drawing has a connected simple supergraph on the same vertex type that still admits such a drawing; its edge set contains the original edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_6fae641e_69bd_437f_8912_51466427af04_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
