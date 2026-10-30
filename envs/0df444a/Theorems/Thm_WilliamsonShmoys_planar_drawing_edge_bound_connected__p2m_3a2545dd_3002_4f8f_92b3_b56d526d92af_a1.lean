-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_connected__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:43:18.837065+00:00
-- url     : https://prove2.me/theorems/23b3a0cc-5638-419d-bfba-72594a7803ae
-- title:
--   Connected planar drawing edge bound, including small cases
-- statement:
--   A connected graph with a crossing-free drawing has at most 3n−6 edges when n≥3; for n<3 it has at most the complete-graph edge count. This supplies the component-level estimate needed by the summation step, including the small cases. The independent proof route is Euler’s formula followed by face-degree counting, with the small cases handled directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_connected__p2m_3a2545dd_3002_4f8f_92b3_b56d526d92af_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    G.edgeSet.ncard <= if 3 <= Fintype.card V then 3 * Fintype.card V - 6 else Fintype.card V * (Fintype.card V - 1) / 2 := by
  sorry
