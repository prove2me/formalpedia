-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:07:19.900982+00:00
-- url     : https://prove2.me/theorems/f2ed2b18-15b8-4e88-a259-a14554d3a010
-- title:
--   Maximal drawable graphs attain the Euler lower bound
-- statement:
--   A maximal drawable simple graph on at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
