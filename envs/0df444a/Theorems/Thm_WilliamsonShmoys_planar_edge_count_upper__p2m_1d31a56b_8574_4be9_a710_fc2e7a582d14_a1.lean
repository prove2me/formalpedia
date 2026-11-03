-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:02:53.511225+00:00
-- url     : https://prove2.me/theorems/8555a31b-9435-47a6-94cc-80670b8cc7a7
-- title:
--   Planar graph edge upper bound
-- statement:
--   Any simple graph with the stated crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
