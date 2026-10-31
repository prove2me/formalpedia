-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:19.137538+00:00
-- url     : https://prove2.me/theorems/e546a1c1-10cc-476b-a894-225ced90c5fe
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V| − 6 edges. This is the upper bound obtained from Euler’s formula and face-degree counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b387e51f_12e6_457e_b8c7_5aeeed4116ef_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
