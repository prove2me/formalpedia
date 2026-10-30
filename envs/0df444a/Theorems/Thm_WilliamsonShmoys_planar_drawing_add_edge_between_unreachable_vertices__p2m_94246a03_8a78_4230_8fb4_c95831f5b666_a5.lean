-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable_vertices__p2m_94246a03_8a78_4230_8fb4_c95831f5b666_a5
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices__p2m_94246a03_8a78_4230_8fb4_c95831f5b666_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:21.34999+00:00
-- url     : https://prove2.me/theorems/d4cb2bc0-fb23-40e7-8d2f-240edd4881b8
-- title:
--   Planar drawing extension across unreachable vertices
-- statement:
--   For a finite graph with a crossing-free drawing, any two vertices in different connected components can be joined by a new edge while retaining a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_between_unreachable_vertices__p2m_94246a03_8a78_4230_8fb4_c95831f5b666_a5 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (u v : V) (hUnreach : ¬ M.Reachable u v) : ∃ N : SimpleGraph V, M ≤ N ∧ N.Adj u v ∧ HasPlanarDrawingOn N := by sorry
