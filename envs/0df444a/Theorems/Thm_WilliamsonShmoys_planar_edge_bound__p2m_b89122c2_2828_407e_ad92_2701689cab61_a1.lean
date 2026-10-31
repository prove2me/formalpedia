-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:40.645202+00:00
-- url     : https://prove2.me/theorems/172ec1a1-67dd-48ed-9b1c-20de26385b63
-- title:
--   Planar graph edge upper bound
-- statement:
--   For a finite simple graph with at least three vertices, a crossing-free drawing implies the standard planar edge upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound__p2m_b89122c2_2828_407e_ad92_2701689cab61_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
