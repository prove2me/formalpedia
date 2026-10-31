-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:04.662192+00:00
-- url     : https://prove2.me/theorems/54a1693d-5f6f-41b0-b799-793fe1e71489
-- title:
--   Connect components of a planar drawing by adding edges
-- statement:
--   A finite simple graph with a crossing-free drawing can be extended, on the same vertex set, to a connected simple graph that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, Z ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
