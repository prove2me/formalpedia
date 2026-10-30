-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:45.746662+00:00
-- url     : https://prove2.me/theorems/0d714fcf-7da8-48c8-afc4-fedf819778b0
-- title:
--   Maximal drawable supergraph on a finite vertex type
-- statement:
--   Every finite graph with a crossing-free drawing has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
