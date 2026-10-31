-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_join_unreachable_components__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
-- name    : WilliamsonShmoys.planar_join_unreachable_components__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:12:52.727971+00:00
-- url     : https://prove2.me/theorems/5706fb97-513c-4058-b58a-e83be5bb134e
-- title:
--   Join unreachable components in a planar drawing
-- statement:
--   Given a crossing-free drawing and two distinct vertices in different connected components, the graph can be redrawn with an added edge between them while preserving planarity; the resulting graph is a strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_join_unreachable_components__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (u v : V) (huv : u ≠ v) (hUnreachable : ¬ L.Reachable u v) : ∃ N : SimpleGraph V, L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ N.Adj u v ∧ ¬ N ≤ L := by sorry
