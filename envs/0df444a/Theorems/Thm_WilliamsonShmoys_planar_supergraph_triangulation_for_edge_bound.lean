-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:59:37.514992+00:00
-- url     : https://prove2.me/theorems/5164bdb5-f88b-47a6-b9f7-561ca2e2d817
-- title:
--   Triangulating a finite planar graph on its existing vertices
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertices with exactly `3 |V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
