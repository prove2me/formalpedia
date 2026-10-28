-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_triangulation_extension
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:41:01.921016+00:00
-- url     : https://prove2.me/theorems/242dfd37-3f37-44d0-8518-cb1f54f67a66
-- title:
--   Extension of a planar drawing to a triangulation
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices whose edge count is three times the number of vertices minus six. The child removes the geometric augmentation and Euler formula work from the parent. A proof can add noncrossing edges between components and across faces until the embedding is triangulated, then apply Euler's formula. Its boundary condition is `|V| ≥ 3`; establishing this extension for the exact continuous-arc drawing predicate is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
