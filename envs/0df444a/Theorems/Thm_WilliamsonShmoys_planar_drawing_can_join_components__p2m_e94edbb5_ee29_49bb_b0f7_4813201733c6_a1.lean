-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_can_join_components__p2m_e94edbb5_ee29_49bb_b0f7_4813201733c6_a1
-- name    : WilliamsonShmoys.planar_drawing_can_join_components__p2m_e94edbb5_ee29_49bb_b0f7_4813201733c6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:35.257301+00:00
-- url     : https://prove2.me/theorems/b040671a-9a8e-4ac4-8063-016043362478
-- title:
--   A disconnected planar drawing admits a drawable strict supergraph
-- statement:
--   If a finite graph on the given ordered vertex type has a planar drawing and is disconnected, then some drawable supergraph on the same vertex type strictly extends it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_can_join_components__p2m_e94edbb5_ee29_49bb_b0f7_4813201733c6_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hDisc : ¬ H.Connected) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H := by sorry
