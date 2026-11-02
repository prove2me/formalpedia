-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:10.123822+00:00
-- url     : https://prove2.me/theorems/02da0ff6-1020-4ffd-8f79-c5b3eb2fc9a4
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Any finite graph with a crossing-free drawing on the given ordered vertex type has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G := by sorry
