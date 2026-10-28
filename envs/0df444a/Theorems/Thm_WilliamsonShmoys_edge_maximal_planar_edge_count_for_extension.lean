-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_for_extension
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_for_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:37:15.814957+00:00
-- url     : https://prove2.me/theorems/dc0151f5-7cac-4f76-bae5-71848a1ab31f
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A planar simple graph on at least three vertices that is maximal under planar edge extensions has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_for_extension {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → J.edgeSet ⊆ K.edgeSet → K.edgeSet = J.edgeSet) : J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
