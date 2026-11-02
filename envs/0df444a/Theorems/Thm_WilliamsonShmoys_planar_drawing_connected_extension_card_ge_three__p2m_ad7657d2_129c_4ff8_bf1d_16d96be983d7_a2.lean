-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_card_ge_three__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_card_ge_three__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:42.957419+00:00
-- url     : https://prove2.me/theorems/230e911d-c89d-4af8-9461-b4f56004db81
-- title:
--   Connect a planar drawing with at least three vertices
-- statement:
--   A finite graph with a crossing-free drawing and at least three vertices has a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_card_ge_three__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ HasPlanarDrawingOn G := by sorry
