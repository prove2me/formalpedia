-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximalExtension__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
-- name    : WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:38.163658+00:00
-- url     : https://prove2.me/theorems/6227bc6c-7904-4dee-bf7b-4cbae8a575f3
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every graph with a planar drawing on a finite vertex type has a planar drawn supergraph on the same vertices that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by sorry
