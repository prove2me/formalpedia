-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_min_degree_two_edge_bound__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
-- name    : WilliamsonShmoys.planar_min_degree_two_edge_bound__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:34.963645+00:00
-- url     : https://prove2.me/theorems/91c2a078-2934-42b0-a2de-624c6c24d6cd
-- title:
--   Edge bound for planar graphs of minimum degree two
-- statement:
--   A connected simple graph with a crossing-free drawing, at least three vertices, and at least two neighbors at every vertex has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_min_degree_two_edge_bound__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 <= Fintype.card V)
    (hdegree : ∀ v : V, 2 <= (K.neighborSet v).ncard) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
