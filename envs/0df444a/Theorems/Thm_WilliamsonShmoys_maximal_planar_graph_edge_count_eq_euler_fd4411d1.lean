-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_eq_euler_fd4411d1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_eq_euler_fd4411d1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:21:42.400525+00:00
-- url     : https://prove2.me/theorems/c7f98cb4-0a35-45b3-9515-2e6b4713a1c4
-- title:
--   Euler edge count for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_eq_euler_fd4411d1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H) : 3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
