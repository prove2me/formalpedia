-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:05.692882+00:00
-- url     : https://prove2.me/theorems/a0a9770d-b636-48de-8b32-1b32b62691e8
-- title:
--   An edge-maximal planar graph is connected
-- statement:
--   A finite graph with a crossing-free drawing that is maximal under edge inclusion among planar supergraphs on the same vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      HasPlanarDrawingOn L →
      ∀ u v, L.Adj u v → K.Adj u v) :
    K.Connected := by sorry
