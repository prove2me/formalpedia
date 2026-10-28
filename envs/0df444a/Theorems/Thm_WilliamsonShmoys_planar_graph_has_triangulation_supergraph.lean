-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:09:14.479731+00:00
-- url     : https://prove2.me/theorems/94348bb4-0897-41cb-a4e2-91f9fb7adb36
-- title:
--   Planar graphs extend to a triangulation on the same vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_graph_has_triangulation_supergraph {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : ∃ M : SimpleGraph V, G <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ 3 * Fintype.card V - 6 = M.edgeSet.ncard := by sorry
