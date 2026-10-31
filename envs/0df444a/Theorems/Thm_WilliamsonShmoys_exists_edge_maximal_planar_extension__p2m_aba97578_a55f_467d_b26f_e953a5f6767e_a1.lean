-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:28.323912+00:00
-- url     : https://prove2.me/theorems/b4d9d994-9c3d-480d-8aaa-85ca7382f67c
-- title:
--   Existence of an edge-maximal planar extension
-- statement:
--   Every finite simple graph with a crossing-free drawing is contained in a planar graph on the same vertices that is maximal under planar supergraph inclusion, and its edge count is no smaller than the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  sorry
