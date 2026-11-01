-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:39.702201+00:00
-- url     : https://prove2.me/theorems/6264da0c-994c-4857-980f-a6ef7e378206
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite fixed vertex type has a drawable supergraph on that same type which is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ea7a71ed_13b1_4c29_adb9_6de531e96387_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn M →
        L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset ⊆ L.edgeFinset := by sorry
