-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_some_edge_when_disconnected__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a2
-- name    : WilliamsonShmoys.planar_add_some_edge_when_disconnected__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:09.444264+00:00
-- url     : https://prove2.me/theorems/28a8d91f-acdb-4d70-bde6-d0e0f7e29c29
-- title:
--   A disconnected planar drawing admits a missing edge
-- statement:
--   Every nonempty finite disconnected graph with a crossing-free drawing has a crossing-free supergraph obtained by adding at least one previously absent edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_some_edge_when_disconnected__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (hV : 0 < Fintype.card V) (hDisconnected : ¬ H.Connected) : ∃ G : SimpleGraph V, H ≤ G ∧ ∃ u v : V, u ≠ v ∧ ¬ H.Adj u v ∧ G.Adj u v ∧ HasPlanarDrawingOn G := by sorry
