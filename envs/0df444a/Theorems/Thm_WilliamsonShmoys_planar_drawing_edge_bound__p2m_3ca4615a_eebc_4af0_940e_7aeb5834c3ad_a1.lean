-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:34.262625+00:00
-- url     : https://prove2.me/theorems/4c6ac7d0-01db-4ee7-b1fb-bccb2c4343c5
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_3ca4615a_eebc_4af0_940e_7aeb5834c3ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
