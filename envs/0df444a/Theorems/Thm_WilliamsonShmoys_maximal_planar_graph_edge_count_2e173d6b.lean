-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_2e173d6b
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_2e173d6b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:36:44.968877+00:00
-- url     : https://prove2.me/theorems/c5c6f6ee-20d4-445b-8462-a60e18f23410
-- title:
--   An inclusion-maximal planar graph has 3n − 6 edges
-- statement:
--   An inclusion-maximal planar graph on a finite vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_2e173d6b
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
