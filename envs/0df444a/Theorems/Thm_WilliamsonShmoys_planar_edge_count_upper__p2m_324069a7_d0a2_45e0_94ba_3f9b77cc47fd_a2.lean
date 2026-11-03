-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:38:59.329554+00:00
-- url     : https://prove2.me/theorems/6f6a4225-6fc3-4c15-be9a-75786ea7ae4b
-- title:
--   Planar graph edge-count upper bound
-- statement:
--   Any graph on at least three vertices with the specified crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
