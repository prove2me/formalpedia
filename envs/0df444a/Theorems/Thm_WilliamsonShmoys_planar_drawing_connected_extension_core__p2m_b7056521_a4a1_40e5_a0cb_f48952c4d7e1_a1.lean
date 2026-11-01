-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:09.795203+00:00
-- url     : https://prove2.me/theorems/16420d1a-8336-4ecd-8bbd-58603af5ab15
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Every finite graph with a crossing-free drawing on its ordered vertex type has a connected planar supergraph on the same vertex type. This removes the edge-count bookkeeping and the target's unnecessary lower bound on the number of vertices, leaving the geometric component-joining argument as the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  sorry
