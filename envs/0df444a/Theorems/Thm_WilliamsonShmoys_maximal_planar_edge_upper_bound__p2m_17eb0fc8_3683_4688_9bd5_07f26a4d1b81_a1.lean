-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:54.233659+00:00
-- url     : https://prove2.me/theorems/b9750e78-67e8-4f3e-9a0d-8a6e9da3267c
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most 3n−6 edges. This is the standard planar edge bound, obtained from Euler’s formula and the lower bound of three on face-boundary lengths.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_17eb0fc8_3683_4688_9bd5_07f26a4d1b81_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * (Fintype.card V - 2) := by sorry
