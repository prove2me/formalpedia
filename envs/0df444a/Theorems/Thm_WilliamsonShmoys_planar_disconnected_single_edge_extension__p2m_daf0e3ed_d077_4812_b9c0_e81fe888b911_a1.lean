-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_single_edge_extension__p2m_daf0e3ed_d077_4812_b9c0_e81fe888b911_a1
-- name    : WilliamsonShmoys.planar_disconnected_single_edge_extension__p2m_daf0e3ed_d077_4812_b9c0_e81fe888b911_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:02.029017+00:00
-- url     : https://prove2.me/theorems/864f1371-5a05-4a46-954d-5d68a77fa253
-- title:
--   Extend a disconnected planar graph by one edge
-- statement:
--   Every disconnected graph with a planar drawing admits a planar extension obtained by adding exactly one edge between two distinct vertices that were not adjacent in the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_single_edge_extension__p2m_daf0e3ed_d077_4812_b9c0_e81fe888b911_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hdisc : ¬ H.Connected) : ∃ G : SimpleGraph V, ∃ u : V, ∃ v : V, u ≠ v ∧ ¬ H.Adj u v ∧ H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v ∧ ∀ {x y : V}, G.Adj x y → H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
