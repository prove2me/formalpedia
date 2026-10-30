-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulation_edge_count
-- name    : WilliamsonShmoys.exists_planar_supergraph_with_triangulation_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:23:44.379327+00:00
-- url     : https://prove2.me/theorems/4c56831b-cd4b-4018-abba-9b024fb1e355
-- title:
--   Planar extension with triangulation edge count
-- statement:
--   Every graph with a planar drawing on at least three vertices has a planar supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_with_triangulation_edge_count {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
