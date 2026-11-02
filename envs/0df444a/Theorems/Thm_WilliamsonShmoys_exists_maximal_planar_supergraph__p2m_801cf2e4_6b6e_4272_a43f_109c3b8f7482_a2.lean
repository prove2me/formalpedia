-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:05.649146+00:00
-- url     : https://prove2.me/theorems/7dd72d83-34f6-4f08-ba9a-4bb87d91a259
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Given a finite graph with a crossing-free drawing, there is a planar supergraph on the same vertices that is maximal under edge inclusion among planar graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v := by sorry
