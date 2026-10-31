-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension__p2m_9c1c6a07_df32_48f2_a3fa_6413055e7fe1_a1
-- name    : WilliamsonShmoys.planar_graph_triangulation_extension__p2m_9c1c6a07_df32_48f2_a3fa_6413055e7fe1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:43:33.118623+00:00
-- url     : https://prove2.me/theorems/a546b4df-cdfe-4033-ada4-bee990d9e0a1
-- title:
--   Triangulating a planar graph by adding edges
-- statement:
--   Every drawable simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_triangulation_extension__p2m_9c1c6a07_df32_48f2_a3fa_6413055e7fe1_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 <= Fintype.card V) : ∃ S : SimpleGraph V, R <= S ∧ HasPlanarDrawingOn S ∧ S.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
