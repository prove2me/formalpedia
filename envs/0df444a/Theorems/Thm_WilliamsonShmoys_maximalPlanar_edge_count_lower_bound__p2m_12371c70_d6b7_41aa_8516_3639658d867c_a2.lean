-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_edge_count_lower_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
-- name    : WilliamsonShmoys.maximalPlanar_edge_count_lower_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:07.213184+00:00
-- url     : https://prove2.me/theorems/93f75d0b-1a3e-40b2-bf9d-97f189fb09d9
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   If no planar supergraph on the same vertices can strictly add edges, then a graph with at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximalPlanar_edge_count_lower_bound__p2m_12371c70_d6b7_41aa_8516_3639658d867c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
