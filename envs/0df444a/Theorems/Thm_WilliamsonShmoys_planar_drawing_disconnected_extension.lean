-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension
-- name    : WilliamsonShmoys.planar_drawing_disconnected_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T02:08:46.50371+00:00
-- url     : https://prove2.me/theorems/0a2854ae-1955-4104-a6b5-3c207989e09d
-- title:
--   Extend a disconnected planar drawing
-- statement:
--   Every disconnected finite graph with a crossing-free drawing has a strictly larger supergraph on the same vertices that also has a crossing-free drawing. The independent proof route is to add an arc between two components through the common exterior face, avoiding the finite existing drawing. This removes the geometric obstacle needed by maximality; routing such an arc while satisfying the predicate’s endpoint and intersection conditions is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (A : SimpleGraph V)
    (hA : WilliamsonShmoys.HasPlanarDrawingOn A)
    (hdisconnected : ¬ A.Connected) :
    ∃ B : SimpleGraph V,
      A ≤ B ∧
      WilliamsonShmoys.HasPlanarDrawingOn B ∧
      A.edgeSet.ncard < B.edgeSet.ncard := by sorry
