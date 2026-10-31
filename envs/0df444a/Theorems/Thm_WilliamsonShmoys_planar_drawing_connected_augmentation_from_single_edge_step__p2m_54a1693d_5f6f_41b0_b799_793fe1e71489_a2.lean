-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_from_single_edge_step__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_from_single_edge_step__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:08.082254+00:00
-- url     : https://prove2.me/theorems/f115a162-ba9a-42c8-aff3-d83e53de475c
-- title:
--   Finite maximal extension yields a connected planar supergraph
-- statement:
--   On a finite vertex type, if each disconnected graph with a planar drawing has a strict planar supergraph on the same vertices, then every planar graph has a connected planar supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_from_single_edge_step__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) (hStep : ∀ (G : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected → ∃ H : SimpleGraph V, G ≤ H ∧ ¬ H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ H : SimpleGraph V, Z ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
