-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_supergraph_of_property__p2m_8a206f96_b3dd_4ad6_9517_cbf07b9eb0ad_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_supergraph_of_property__p2m_8a206f96_b3dd_4ad6_9517_cbf07b9eb0ad_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:37:46.871176+00:00
-- url     : https://prove2.me/theorems/1db78285-89d9-49bd-a745-5e1daaf30ce7
-- title:
--   Finite graph properties admit edge-maximal supergraphs
-- statement:
--   For any property of graphs on a finite linearly ordered vertex type, if a graph satisfies the property, it has a property-satisfying supergraph on the same vertices that is maximal by edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_supergraph_of_property__p2m_8a206f96_b3dd_4ad6_9517_cbf07b9eb0ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hN : P N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        P K →
        K.edgeSet ⊆ M.edgeSet := by sorry
