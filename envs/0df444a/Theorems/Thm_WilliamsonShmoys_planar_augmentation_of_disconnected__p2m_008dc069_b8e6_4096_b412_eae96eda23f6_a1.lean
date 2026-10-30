-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_of_disconnected__p2m_008dc069_b8e6_4096_b412_eae96eda23f6_a1
-- name    : WilliamsonShmoys.planar_augmentation_of_disconnected__p2m_008dc069_b8e6_4096_b412_eae96eda23f6_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T08:53:53.050981+00:00
-- url     : https://prove2.me/theorems/1b610d16-398e-4171-ae3e-0138b0edcfb3
-- title:
--   A disconnected planar drawing admits a strict planar extension
-- statement:
--   For a finite linearly ordered vertex type, any disconnected graph with a crossing-free drawing has a strictly larger graph on the same vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_of_disconnected__p2m_008dc069_b8e6_4096_b412_eae96eda23f6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hNotConnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ L ≤ K := by sorry
