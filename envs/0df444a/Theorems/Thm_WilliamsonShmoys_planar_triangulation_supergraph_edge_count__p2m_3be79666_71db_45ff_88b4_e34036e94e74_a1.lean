-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_3be79666_71db_45ff_88b4_e34036e94e74_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_3be79666_71db_45ff_88b4_e34036e94e74_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:18.565897+00:00
-- url     : https://prove2.me/theorems/3bbe118b-2c52-4e44-a40f-aa9dcfe8d0b0
-- title:
--   A drawable graph has a drawable completion with the maximal planar edge count
-- statement:
--   For every finite drawable simple graph with at least three vertices, there is a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This isolates the topological completion and Euler-counting work; maximality in the parent then forces the completion to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_3be79666_71db_45ff_88b4_e34036e94e74_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
