-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- name    : WilliamsonShmoys.planar_connected_supergraph__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:44:57.071708+00:00
-- url     : https://prove2.me/theorems/801cf2e4-6b6e-4272-a43f-109c3b8f7482
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Every finite simply drawn planar graph can be extended, using only its existing vertices, to a connected graph that still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph__p2m_f0f39874_5ae5_48cf_ae7d_0d6801141c64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      K.Connected ∧ HasPlanarDrawingOn K := by sorry
