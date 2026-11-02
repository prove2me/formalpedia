-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:01:48.788267+00:00
-- url     : https://prove2.me/theorems/1869d2b3-4acb-4df1-b926-664515403053
-- title:
--   Edge bound for any finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges. This strengthens the target by requiring no maximality assumption. It can be proved by augmenting a planar embedding to a triangulation and applying Euler’s formula with face-edge counting; the formal work is to connect the supplied arc-based definition to that argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  sorry
