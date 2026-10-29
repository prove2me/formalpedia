-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- name    : WilliamsonShmoys.planar_connected_augmentation__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:32.566975+00:00
-- url     : https://prove2.me/theorems/8865e8a3-5dd6-4b37-9810-2347390bab67
-- title:
--   Connected planar augmentation of a drawable graph
-- statement:
--   Any finite drawable graph can be extended, without adding vertices, to a connected drawable simple graph containing all its edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_connected_augmentation__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
