-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_one_step_merge_with_card_bound
-- name    : WilliamsonShmoys.planar_disconnected_one_step_merge_with_card_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:25:35.882834+00:00
-- url     : https://prove2.me/theorems/bbe51f7a-de77-464f-9208-024da03a3910
-- title:
--   Add a planar edge between distinct components with at least three vertices
-- statement:
--   A disconnected graph with at least three vertices and a drawing satisfying the specified planarity predicate can be enlarged by an edge joining distinct original components while retaining that drawing property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_disconnected_one_step_merge_with_card_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
