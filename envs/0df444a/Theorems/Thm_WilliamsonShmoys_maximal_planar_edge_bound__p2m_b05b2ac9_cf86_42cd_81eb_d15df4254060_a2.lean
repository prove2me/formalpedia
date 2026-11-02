-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:21:39.999202+00:00
-- url     : https://prove2.me/theorems/d59a8e60-bd9e-4339-9c63-4718b5d88d29
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A maximal planar simple graph on a finite vertex type with at least three vertices has at most `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hMaximal : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
