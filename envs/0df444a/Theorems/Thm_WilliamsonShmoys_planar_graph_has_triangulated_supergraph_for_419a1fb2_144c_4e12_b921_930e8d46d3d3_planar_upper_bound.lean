-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_for_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_supergraph_for_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:25:08.012659+00:00
-- url     : https://prove2.me/theorems/7e0405ab-21ca-48e3-b252-8778a4e47e59
-- title:
--   Same-vertex triangulated planar completion
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained, on the same vertex set, in a drawable graph with exactly 3|V|−6 edges; the inclusion also supplies the edge-count monotonicity needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_supergraph_for_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
