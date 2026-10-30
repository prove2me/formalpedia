-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_maximal_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_maximal_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:58:58.687623+00:00
-- url     : https://prove2.me/theorems/fef310bd-98ca-4c86-8c3c-2dbd49a090d7
-- title:
--   Maximal drawable graphs meet the planar edge-count lower bound
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable graphs on the same vertex set has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3_maximal_lower_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
