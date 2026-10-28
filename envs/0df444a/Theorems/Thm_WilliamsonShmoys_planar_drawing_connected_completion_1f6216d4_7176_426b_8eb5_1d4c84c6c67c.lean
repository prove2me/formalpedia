-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- name    : WilliamsonShmoys.planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:33:04.386109+00:00
-- url     : https://prove2.me/theorems/5e408e15-12d4-48eb-8021-1b7dc829dd11
-- title:
--   Connect components while preserving a planar drawing
-- statement:
--   Any graph with the given finite crossing-free drawing can be extended to a connected graph on the same vertices with a crossing-free drawing and at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_completion_1f6216d4_7176_426b_8eb5_1d4c84c6c67c
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
