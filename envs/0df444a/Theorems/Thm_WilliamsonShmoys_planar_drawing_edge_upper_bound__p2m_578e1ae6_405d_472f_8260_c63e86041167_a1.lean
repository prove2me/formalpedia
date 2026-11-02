-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:07:40.799664+00:00
-- url     : https://prove2.me/theorems/e26f4eeb-ea90-4bc7-9f3f-02f85b28272b
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Any graph on at least three vertices with a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_578e1ae6_405d_472f_8260_c63e86041167_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
