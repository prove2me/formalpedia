-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_augmentation__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
-- name    : WilliamsonShmoys.planarDrawing_connected_augmentation__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:55.402544+00:00
-- url     : https://prove2.me/theorems/e22a771a-7e28-4296-9438-b0a9d74716aa
-- title:
--   Connect a planar drawing by adding edges
-- statement:
--   A drawable finite simple graph on at least three vertices can be extended, on the same vertex set, to a connected drawable graph whose edge count is at least as large.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connected_augmentation__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      H.Connected ∧ HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
