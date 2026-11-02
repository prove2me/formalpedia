-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_adds_edge_of_not_connected__p2m_28f50d30_117d_4a63_8d20_afb26b4b003d_a1
-- name    : WilliamsonShmoys.planar_extension_adds_edge_of_not_connected__p2m_28f50d30_117d_4a63_8d20_afb26b4b003d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:54.251411+00:00
-- url     : https://prove2.me/theorems/0d5204bf-176f-424e-aee7-a71e09390474
-- title:
--   A disconnected planar drawing admits a strict drawable extension
-- statement:
--   For a drawable graph on at least three vertices, disconnectedness allows adding at least one edge while retaining a crossing-free drawing on the same vertex set. This isolates the geometric augmentation step; maximality then rules out disconnectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_extension_adds_edge_of_not_connected__p2m_28f50d30_117d_4a63_8d20_afb26b4b003d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hdis : ¬ G.Connected) :
    ∃ J : SimpleGraph V, G ≤ J ∧ G ≠ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J := by sorry
