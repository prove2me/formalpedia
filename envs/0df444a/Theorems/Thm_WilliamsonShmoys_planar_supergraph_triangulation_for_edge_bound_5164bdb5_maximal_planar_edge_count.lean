-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_planar_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_planar_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:56:44.322971+00:00
-- url     : https://prove2.me/theorems/82152a25-b0ed-4245-9a1a-e152a628b88f
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices whose drawing admits no planar supergraph on the same vertices has exactly `3|V| - 6` edges. The proof must relate the supplied continuous-arc drawing to planar faces, show maximality forces every face to be triangular, and apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
