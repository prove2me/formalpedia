-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
-- name    : WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:50:51.059274+00:00
-- url     : https://prove2.me/theorems/cfe9aff8-83c0-4052-b6d2-ba6730520dd6
-- title:
--   Planar edge-count upper bound for the target graph
-- statement:
--   A drawable finite simple graph with at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
