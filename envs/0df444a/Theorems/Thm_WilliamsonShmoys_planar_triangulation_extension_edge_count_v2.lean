-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count_v2
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:10:59.656982+00:00
-- url     : https://prove2.me/theorems/3c455896-e7e4-4584-9894-4be39c6ad6e1
-- title:
--   Triangulation extension with exact planar edge count
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges. This removes the whole maximality-to-edge-count step from the parent; its proof requires planar augmentation and a planar edge count for the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count_v2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 <= Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M <= N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧ 3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
