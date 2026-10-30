-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_lower_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_lower_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:12.555629+00:00
-- url     : https://prove2.me/theorems/3a9c85e5-093c-48f7-b644-f83c4d4db2f4
-- title:
--   Lower edge bound for an edge-maximal planar graph
-- statement:
--   An edge-maximal planar graph on at least three vertices has at least 3|V| − 6 edges. The proof route is to show maximality forces connectedness and triangular faces, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_lower_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hMax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  sorry
