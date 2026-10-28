-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_graph_euler_bound
-- name    : WilliamsonShmoys.edge_maximal_drawable_graph_euler_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:25:52.236512+00:00
-- url     : https://prove2.me/theorems/151c6352-6b6b-4eef-b00d-fbbc0540e553
-- title:
--   Euler edge bound for an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three finite vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_drawable_graph_euler_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
