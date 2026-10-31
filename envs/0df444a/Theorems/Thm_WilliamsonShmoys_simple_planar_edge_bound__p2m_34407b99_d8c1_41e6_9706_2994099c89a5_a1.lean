-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- name    : WilliamsonShmoys.simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:51.813216+00:00
-- url     : https://prove2.me/theorems/6e30398e-7f8d-44b8-bb51-ffb2d64a0829
-- title:
--   Simple planar edge bound
-- statement:
--   A connected simple graph with at least three vertices and the supplied planar drawing has at most `3V − 6` edges, expressed without truncated natural subtraction as `E + 6 ≤ 3V`. This reusable planar density bound, combined with Euler’s equation, gives the target’s face-incidence inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
