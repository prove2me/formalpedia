-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_connected__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:32.045256+00:00
-- url     : https://prove2.me/theorems/5d9b8ff2-1349-4ea9-a2d4-f406c9d22c5b
-- title:
--   Edge bound for a connected simple planar graph
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing has at most three times its vertex count minus six edges. Prove this by deriving a plane embedding, applying Euler’s formula, and counting at least three edge sides per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
