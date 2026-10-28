-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension_edge_count
-- name    : WilliamsonShmoys.exists_triangulated_planar_extension_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:06:11.273753+00:00
-- url     : https://prove2.me/theorems/777ec98c-98f4-4f6a-b3be-b4ac80a215e9
-- title:
--   Planar extension with triangulation edge count
-- statement:
--   Any finite simple planar graph with at least three vertices is a subgraph of a planar graph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_planar_extension_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
