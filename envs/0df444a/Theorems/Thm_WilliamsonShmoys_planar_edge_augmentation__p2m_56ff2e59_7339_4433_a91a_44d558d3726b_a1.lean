-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:31:19.386342+00:00
-- url     : https://prove2.me/theorems/e279d529-0df7-4422-b7c0-ab730b7394ba
-- title:
--   Add an edge below the planar triangulation count
-- statement:
--   For a finite simple graph on at least three vertices, if its planar drawing has fewer than 3|V|−6 edges, it can be extended by one edge while retaining a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard = K.edgeSet.ncard + 1 := by sorry
