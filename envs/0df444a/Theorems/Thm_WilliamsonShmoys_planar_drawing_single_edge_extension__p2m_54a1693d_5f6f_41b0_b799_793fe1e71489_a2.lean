-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_single_edge_extension__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
-- name    : WilliamsonShmoys.planar_drawing_single_edge_extension__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:10.495695+00:00
-- url     : https://prove2.me/theorems/6c8792df-3052-4680-9206-6fff099f2f1e
-- title:
--   Strictly extend a disconnected planar drawing
-- statement:
--   Any disconnected graph with the supplied crossing-free drawing has a strict planar supergraph on the same vertices. This is the geometric extension obligation needed to connect components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_single_edge_extension__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hDisconnected : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ ¬ H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
