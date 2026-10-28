-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- name    : WilliamsonShmoys.planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:55:40.628763+00:00
-- url     : https://prove2.me/theorems/cd75542c-b2a4-4b5f-b583-b57082c26eaf
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   A crossing-free drawing remains a crossing-free drawing of any subgraph on the same vertex type, using the original vertex placement and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
