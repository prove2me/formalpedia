-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:16.719949+00:00
-- url     : https://prove2.me/theorems/f1a10c6f-98ea-4f43-9f3f-2fa486717043
-- title:
--   Upper edge bound for a simple planar graph
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_620608d3_0799_426b_beeb_eff4e8e41716_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
