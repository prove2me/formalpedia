-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_at_unreachable_pair__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a1
-- name    : WilliamsonShmoys.planar_add_edge_at_unreachable_pair__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:15.817024+00:00
-- url     : https://prove2.me/theorems/5043418e-4ebe-43f6-bf7b-89868a1bb747
-- title:
--   Planar augmentation at an unreachable pair
-- statement:
--   Given a crossing-free drawing and two vertices in distinct connected components, one can add an edge between them while preserving a crossing-free drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_edge_at_unreachable_pair__p2m_f7639c38_a73f_4cc2_ae8d_a0f2b8768f46_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) (u v : V) (hUnreachable : ¬ H.Reachable u v) : ∃ G : SimpleGraph V, H ≤ G ∧ G ≠ H ∧ HasPlanarDrawingOn G := by sorry
