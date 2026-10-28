-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_of_not_connected
-- name    : WilliamsonShmoys.planar_extension_of_not_connected
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T03:11:05.768613+00:00
-- url     : https://prove2.me/theorems/f5e62f70-6c0a-4ec6-9849-be1fc02df722
-- title:
--   A disconnected planar drawing admits a strict planar extension
-- statement:
--   Every disconnected finite graph with a crossing-free drawing on its ordered vertex type has a strictly larger supergraph on the same vertex type that also has a crossing-free drawing. The nonconnectedness hypothesis is retained exactly, including cases where the vertex type is empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_extension_of_not_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hnot : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
