-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_connected_case__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_connected_case__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:11:25.090124+00:00
-- url     : https://prove2.me/theorems/7bba71c9-ccd8-4c5e-9f36-6c106eba0d6c
-- title:
--   Connected planar drawing edge upper bound
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_connected_case__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : N.Connected) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  sorry
