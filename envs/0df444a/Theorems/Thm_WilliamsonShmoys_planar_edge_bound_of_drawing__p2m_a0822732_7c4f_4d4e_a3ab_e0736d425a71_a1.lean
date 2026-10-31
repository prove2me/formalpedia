-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_a0822732_7c4f_4d4e_a3ab_e0736d425a71_a1
-- name    : WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_a0822732_7c4f_4d4e_a3ab_e0736d425a71_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:42:01.808758+00:00
-- url     : https://prove2.me/theorems/85efdcf1-7002-4c36-9c3f-e040848917fe
-- title:
--   Simple planar edge bound from a crossing-free drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_a0822732_7c4f_4d4e_a3ab_e0736d425a71_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
