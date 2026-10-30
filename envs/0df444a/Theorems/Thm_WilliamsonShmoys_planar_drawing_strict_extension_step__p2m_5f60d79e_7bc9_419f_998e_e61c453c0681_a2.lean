-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_step__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
-- name    : WilliamsonShmoys.planar_drawing_strict_extension_step__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:52.295593+00:00
-- url     : https://prove2.me/theorems/fa432a09-dc47-4575-a17d-c2c74cdc2049
-- title:
--   Extend a disconnected finite planar drawing strictly
-- statement:
--   Every disconnected finite graph with the specified crossing-free drawing has a drawable strict supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_strict_extension_step__p2m_5f60d79e_7bc9_419f_998e_e61c453c0681_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hDisconnected : ¬ H.Connected) : ∃ K : SimpleGraph V, H.edgeSet ⊂ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
