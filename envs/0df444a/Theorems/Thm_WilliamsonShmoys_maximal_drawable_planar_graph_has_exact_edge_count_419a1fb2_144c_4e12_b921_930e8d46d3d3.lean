-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- name    : WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:23:56.805088+00:00
-- url     : https://prove2.me/theorems/3dfcf12d-cf70-4249-98dc-599768bb8158
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
