-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:35.389437+00:00
-- url     : https://prove2.me/theorems/69b1ec23-7e07-4ae5-a2a3-1213925ce8f9
-- title:
--   Connected planar extension of a finite drawing
-- statement:
--   Every finite graph with a crossing-free drawing has a connected planar supergraph on the same vertices whose edge set contains the original edge set. The drawing can be connected by adding edges through the complement while preserving the crossing-free conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
