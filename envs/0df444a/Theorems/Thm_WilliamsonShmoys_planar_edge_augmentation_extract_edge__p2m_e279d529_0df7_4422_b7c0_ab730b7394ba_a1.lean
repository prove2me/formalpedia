-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_extract_edge__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_extract_edge__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:39:39.335591+00:00
-- url     : https://prove2.me/theorems/a5baacae-9f8a-4d46-8d07-2c45dbdf2422
-- title:
--   Extract a one-edge extension from a larger supergraph
-- statement:
--   If K is an edge-subgraph of T, K has strictly fewer than 3|V|−6 edges, and T has exactly 3|V|−6 edges, construct a simple graph M by adjoining one edge of T absent from K. The strict inequality and finite edge counts guarantee such an edge; adjoining it preserves simplicity. This removes the bookkeeping from the drawing argument and lets the parent inherit planarity from T only when it selects the final witness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation_extract_edge__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K T : SimpleGraph V)
    (hKT : K.edgeSet ⊆ T.edgeSet)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V)
    (hTcard : T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      M.edgeSet.ncard = K.edgeSet.ncard + 1 := by sorry
