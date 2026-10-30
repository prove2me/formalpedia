-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:57:19.784923+00:00
-- url     : https://prove2.me/theorems/bbe69553-00c5-4ea0-b529-04641759cefa
-- title:
--   Euler edge count for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
