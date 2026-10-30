-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_b74a49f4
-- name    : WilliamsonShmoys.planar_triangulation_extension_b74a49f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:01:43.236303+00:00
-- url     : https://prove2.me/theorems/8e6fe4ee-76fd-4caa-8f38-7058c432af92
-- title:
--   Extend a planar drawing to a triangulated supergraph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a crossing-free supergraph on the same vertices with exactly 3|V|−6 edges, containing at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_triangulation_extension_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
