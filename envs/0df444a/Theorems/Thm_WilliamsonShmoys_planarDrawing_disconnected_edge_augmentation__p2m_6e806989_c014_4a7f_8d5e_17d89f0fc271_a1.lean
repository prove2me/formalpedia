-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_disconnected_edge_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a1
-- name    : WilliamsonShmoys.planarDrawing_disconnected_edge_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:02.323074+00:00
-- url     : https://prove2.me/theorems/da19fde8-c704-497c-943d-81ea3af6a2a9
-- title:
--   Join two drawable components with one edge
-- statement:
--   For a finite drawable graph on at least three vertices that is disconnected, add one edge between components so the resulting graph remains drawable and becomes connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_disconnected_edge_augmentation__p2m_6e806989_c014_4a7f_8d5e_17d89f0fc271_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = K.edgeSet.ncard + 1 := by sorry
