-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:02:31.877607+00:00
-- url     : https://prove2.me/theorems/120b8d49-099c-4729-927b-decab250b8ce
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   A finite graph with at least three vertices and a crossing-free drawing has a connected planar supergraph on the same vertex set. The size hypothesis excludes the empty-type counterexample to the earlier version; the child isolates the geometric augmentation required by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_core__p2m_b7056521_a4a1_40e5_a0cb_f48952c4d7e1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  sorry
