-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
-- name    : WilliamsonShmoys.planar_add_edge_between_components__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:35:33.833695+00:00
-- url     : https://prove2.me/theorems/dad482ed-e722-487b-b00c-3099dd0fc0c7
-- title:
--   Add a planar edge between components
-- statement:
--   If two vertices of a graph with a crossing-free drawing lie in distinct components, one can add an edge between them and obtain a crossing-free drawing of the enlarged graph. This isolates the topological work; a proof route is to place the disconnected components in planar regions and route a new arc through their complementary face regions, then verify the drawing axioms for the new edge and retain the old arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_components__p2m_1532c25a_65bb_404f_a90f_83fae1a22778_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (u v : V) (hnotReachable : ¬ G.Reachable u v) : ∃ H : SimpleGraph V, G < H ∧ H.Adj u v ∧ HasPlanarDrawingOn H := by sorry
