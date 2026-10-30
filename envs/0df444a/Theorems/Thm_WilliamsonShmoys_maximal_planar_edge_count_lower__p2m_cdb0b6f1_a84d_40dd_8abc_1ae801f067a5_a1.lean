-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:53.853961+00:00
-- url     : https://prove2.me/theorems/7f93083e-ff7f-4b04-ad2d-f54588b36aea
-- title:
--   Maximality forces the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V| − 6 edges. The proof route is to show that any drawable graph with fewer edges admits a drawable missing edge, contradicting maximality; equivalently, maximality forces every face of a planar embedding to be triangular.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
