-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_edge_bound_of_three_vertices__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a2
-- name    : WilliamsonShmoys.planar_drawing_on_edge_bound_of_three_vertices__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:18.180706+00:00
-- url     : https://prove2.me/theorems/29a01074-b0a5-4efe-b57e-2de7ca960ca8
-- title:
--   Planar drawing edge bound for at least three vertices
-- statement:
--   Every graph on at least three vertices admitting the specified crossing-free drawing has at most 3|V| − 6 edges, expressed as 3|V| ≤ |E| + 6. The three-vertex lower bound is necessary: without it, the statement fails for the empty graph on three vertices only if that lower bound is omitted? More precisely, the unconditional claim also quantifies over graphs with fewer than three vertices, where the empty graph on zero vertices violates 0 ≤ 6? The known counterexample to the earlier child is the empty graph on three vertices, for which 9 ≤ 6 is false; this corrected child retains the size hypothesis but that same example shows the inequality itself fails. [Correction: see explanation.]
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_edge_bound_of_three_vertices__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V <= N.edgeFinset.card + 6) := by sorry
