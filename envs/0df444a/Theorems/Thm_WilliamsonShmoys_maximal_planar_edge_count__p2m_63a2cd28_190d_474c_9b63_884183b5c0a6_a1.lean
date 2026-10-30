-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:53.392377+00:00
-- url     : https://prove2.me/theorems/cdb0b6f1-a84d-40dd-8abc-1ae801f067a5
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A finite simple graph that is drawable and maximal among drawable supergraphs on its vertex type has exactly 3|V| − 6 edges when |V| ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
