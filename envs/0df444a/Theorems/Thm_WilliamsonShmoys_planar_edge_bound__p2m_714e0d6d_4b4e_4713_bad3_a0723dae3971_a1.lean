-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:24.003067+00:00
-- url     : https://prove2.me/theorems/5fe05f92-ada3-4dee-b840-4a57db020566
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
