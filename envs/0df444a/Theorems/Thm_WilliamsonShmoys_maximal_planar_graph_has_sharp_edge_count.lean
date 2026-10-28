-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_sharp_edge_count
-- name    : WilliamsonShmoys.maximal_planar_graph_has_sharp_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:26:18.958436+00:00
-- url     : https://prove2.me/theorems/f81c96b6-b51d-4165-8b99-52e367cbc589
-- title:
--   Edge-maximal planar graph has sharp edge count
-- statement:
--   A simple graph on at least three vertices that has a planar drawing and admits no strict planar supergraph on the same vertex type has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_has_sharp_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H <= K → K ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
