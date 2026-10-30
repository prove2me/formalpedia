-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count_eq__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
-- name    : WilliamsonShmoys.maximalPlanar_edge_count_eq__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:38.481807+00:00
-- url     : https://prove2.me/theorems/12371c70-d6b7-41aa-8516-3639658d867c
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph on at least three vertices that is maximal under edge-set inclusion among graphs admitting the given planar drawing has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanar_edge_count_eq__p2m_7f93083e_ff7f_4b04_ad2d_f54588b36aea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
