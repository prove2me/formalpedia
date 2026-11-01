-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_from_local_addition__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_from_local_addition__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:48.654889+00:00
-- url     : https://prove2.me/theorems/92ab9f16-2d15-4356-b6df-90082235199d
-- title:
--   Iterate local planar additions to obtain a connected extension
-- statement:
--   A local operation that joins two unreachable vertices by one new edge while preserving a drawing can be iterated on a finite vertex type to produce a connected drawn extension with at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_from_local_addition__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hstep : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          HasPlanarDrawingOn H ∧ G ≤ H ∧
          ∀ x y : V,
            H.Adj x y ↔
              G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
