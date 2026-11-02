-- Prove2me | Theorems.Thm_planar_drawing_has_maximal_planar_extension__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
-- name    : planar_drawing_has_maximal_planar_extension__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:31:24.566043+00:00
-- url     : https://prove2.me/theorems/30717a8b-f004-4e88-a3d7-0eab2997311e
-- title:
--   Extend a drawn graph to a maximal planar supergraph
-- statement:
--   Any finite graph with a crossing-free drawing has a supergraph on the same vertices that is maximal among graphs with such drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem planar_drawing_has_maximal_planar_extension__p2m_c678df30_9cd8_4fa5_9888_0e5b50f2f715_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (K' : SimpleGraph V) (dK' : DecidableRel K'.Adj),
      K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧
        ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
          K' ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K' := by sorry
