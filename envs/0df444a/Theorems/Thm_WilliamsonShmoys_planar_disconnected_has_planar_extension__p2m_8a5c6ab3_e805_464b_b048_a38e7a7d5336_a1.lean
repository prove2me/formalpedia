-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a1
-- name    : WilliamsonShmoys.planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T04:27:07.529997+00:00
-- url     : https://prove2.me/theorems/daf0e3ed-d077-4812-b9c0-e81fe888b911
-- title:
--   A disconnected planar graph has a strict planar extension
-- statement:
--   Every disconnected graph with a crossing-free drawing on a finite linearly ordered vertex type has a crossing-free drawing on the same vertex type after adding at least one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_disconnected_has_planar_extension__p2m_8a5c6ab3_e805_464b_b048_a38e7a7d5336_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) (hdisc : ¬ H.Connected) :
    ∃ G : SimpleGraph V, H ≤ G ∧ HasPlanarDrawingOn G ∧ ¬ G ≤ H := by
  sorry
