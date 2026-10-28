-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph_for_edge_bound_30a2cd75
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T13:38:19.784495+00:00
-- url     : https://prove2.me/theorems/0fd61007-8bd1-403d-b456-4cfc3b5608e0
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertex type, with at least as many edges. The supergraph may use a different drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
