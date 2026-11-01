-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_unreachable__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:53.475389+00:00
-- url     : https://prove2.me/theorems/90606238-5f2e-48e5-b7d6-6d686b1c2a5f
-- title:
--   Add a drawn edge between disconnected components
-- statement:
--   If a finite drawn graph is disconnected, choose vertices in different components and add just the edge between them while preserving a planar drawing and retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_between_unreachable__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hNotConnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v ∧
      ∃ H : SimpleGraph V,
        HasPlanarDrawingOn H ∧ K ≤ H ∧
        ∀ x y : V,
          H.Adj x y ↔
            K.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
