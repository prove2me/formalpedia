-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1
-- name    : WilliamsonShmoys.planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T12:10:19.683236+00:00
-- url     : https://prove2.me/theorems/93958b12-2978-49ef-a2e2-395a87349bb0
-- title:
--   Edge bound for a graph with a planar drawing
-- statement:
--   Every finite simple graph admitting the specified crossing-free drawing has at most 3|V| − 6 edges, expressed as 3|V| ≤ |E| + 6. The inequality also holds for graphs with fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V <= N.edgeFinset.card + 6) := by sorry
