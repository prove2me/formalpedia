-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:04.906107+00:00
-- url     : https://prove2.me/theorems/c9a4a27a-018e-4f14-8723-166da166188f
-- title:
--   Euler upper bound for finite planar graphs
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
