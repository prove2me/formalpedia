-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_b1db10ca_2200_4b55_8753_9bc7a07260c1
-- name    : WilliamsonShmoys.planar_graph_has_triangulated_extension_b1db10ca_2200_4b55_8753_9bc7a07260c1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:05:11.523192+00:00
-- url     : https://prove2.me/theorems/b9be61fe-8c1d-403c-9dc2-d4f84da24c92
-- title:
--   Planar graph extension to a triangulation with exact edge count
-- statement:
--   Every finite graph with at least three vertices that admits the specified planar drawing is a subgraph of a planar graph on the same vertex set with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulated_extension_b1db10ca_2200_4b55_8753_9bc7a07260c1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ 3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by sorry
