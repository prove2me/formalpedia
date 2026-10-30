-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:58:43.37904+00:00
-- url     : https://prove2.me/theorems/cc2f8cc4-dcf7-45b4-b1a9-9e855fdbb0d2
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   An inclusion-maximal drawable graph on a finite linearly ordered vertex type of size at least three has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a9
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hMax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
