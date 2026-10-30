-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
-- name    : WilliamsonShmoys.maximal_drawing_edge_count__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:16.149666+00:00
-- url     : https://prove2.me/theorems/f3b09488-81b3-4c0a-8ec2-c4e84638c6d1
-- title:
--   Count edges in an inclusion-maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly `3|V|−6` edges. The proof route is to show inclusion-maximality forces triangular faces, count face-edge incidences, and apply Euler’s formula. This is the remaining topological and Euler-counting obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.maximal_drawing_edge_count__p2m_287d45f7_8fd6_4d69_bf9c_a1b2fb389f0f_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hMax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
