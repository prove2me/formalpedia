-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
-- name    : WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:59:44.262154+00:00
-- url     : https://prove2.me/theorems/88a23be9-d4b8-4c2f-ae93-4144264bf00e
-- title:
--   Connected planar supergraph with at least as many edges
-- statement:
--   A planar graph on at least three vertices has a connected planar supergraph on the same vertex type with at least as many edges. The supergraph may use a different drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
