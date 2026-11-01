-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:27.68957+00:00
-- url     : https://prove2.me/theorems/40c1c52c-c498-4287-a557-1efecd0d6ca7
-- title:
--   Upper bound on drawable planar graph edges
-- statement:
--   Every drawable simple graph on at least three finite vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
