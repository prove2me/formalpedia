-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_ws
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_ws
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:29:13.538952+00:00
-- url     : https://prove2.me/theorems/b906adce-7899-4066-b059-0588171cafe7
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable graph on a finite linearly ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_ws {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : 3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
