-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:30:35.054188+00:00
-- url     : https://prove2.me/theorems/06b37cfb-5289-4772-9a3d-e9de9d552633
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar simple graph with at least three vertices that has no proper planar supergraph on those vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_edge_count {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
