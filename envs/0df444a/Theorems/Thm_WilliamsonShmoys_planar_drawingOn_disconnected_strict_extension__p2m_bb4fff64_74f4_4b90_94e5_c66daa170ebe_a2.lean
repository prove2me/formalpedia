-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a2
-- name    : WilliamsonShmoys.planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:07:13.996691+00:00
-- url     : https://prove2.me/theorems/a0f2ef0b-cebf-4e8e-ba87-c5e3ec6e107e
-- title:
--   A sufficiently large disconnected planar drawing has a drawable strict extension
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every disconnected graph with a crossing-free drawing has a crossing-free drawing after adding at least one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_disconnected_strict_extension__p2m_bb4fff64_74f4_4b90_94e5_c66daa170ebe_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ M.Connected) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      ¬ N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
