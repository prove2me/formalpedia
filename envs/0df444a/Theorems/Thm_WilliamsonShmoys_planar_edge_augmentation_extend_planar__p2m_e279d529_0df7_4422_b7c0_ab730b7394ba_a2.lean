-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_extend_planar__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a2
-- name    : WilliamsonShmoys.planar_edge_augmentation_extend_planar__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:48:54.651324+00:00
-- url     : https://prove2.me/theorems/f10e52ed-7e34-4f15-bfd4-3ce6b850e38c
-- title:
--   Extract a planar one-edge extension inside a supergraph
-- statement:
--   Given a planar graph T containing K, where T has exactly 3|V|−6 edges and K is strictly below that count, construct a planar graph L containing K with exactly one additional edge. Choose an edge of T absent from K, adjoin it to K, and restrict T’s drawing to the resulting subgraph. This isolates the finite edge-selection and drawing-restriction step from the separate topological task of constructing T.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation_extend_planar__p2m_e279d529_0df7_4422_b7c0_ab730b7394ba_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hKT : K.edgeSet ⊆ T.edgeSet)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V)
    (hTcard : T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard = K.edgeSet.ncard + 1 := by sorry
