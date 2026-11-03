-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count__p2m_24bfc568_7b25_4409_b2ae_c59e72f324da_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_euler_edge_count__p2m_24bfc568_7b25_4409_b2ae_c59e72f324da_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:38.325786+00:00
-- url     : https://prove2.me/theorems/8f4a45b9-f163-4874-a053-f0594b399bd6
-- title:
--   Planar graph extends to a triangulated planar supergraph
-- statement:
--   Every finite drawable simple graph on at least three vertices can be extended, on the same vertex type, to a drawable graph with exactly 3|V|−6 edges. The extension is the triangulation step needed by the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_supergraph_with_euler_edge_count__p2m_24bfc568_7b25_4409_b2ae_c59e72f324da_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ 3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
