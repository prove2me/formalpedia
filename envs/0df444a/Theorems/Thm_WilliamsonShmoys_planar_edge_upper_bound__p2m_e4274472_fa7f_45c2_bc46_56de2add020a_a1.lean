-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:11.573754+00:00
-- url     : https://prove2.me/theorems/d847cb0d-bf38-465c-a743-e30e146fb79e
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Any graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
