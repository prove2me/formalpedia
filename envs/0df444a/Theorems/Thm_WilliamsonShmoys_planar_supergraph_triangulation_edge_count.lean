-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:06:18.289746+00:00
-- url     : https://prove2.me/theorems/ed273cab-be46-4173-847f-eda3a14aa655
-- title:
--   Planar augmentation to a triangulation edge count
-- statement:
--   Every graph with the specified crossing-free drawing and at least three vertices has a planar supergraph on the same vertices whose edge count is the triangulation count 3n−6. This isolates the topological augmentation and Euler-formula work needed by the parent. A proof route is to add noncrossing edges within faces until the embedding is triangulated, then apply Euler’s formula; the three-vertex case yields the triangle. The available local evidence contains the drawing definition and the textbook reference, but no formal augmentation proof to reuse.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
