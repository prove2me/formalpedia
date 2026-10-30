-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_from_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
-- name    : WilliamsonShmoys.planar_completion_from_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:31:24.158519+00:00
-- url     : https://prove2.me/theorems/bd86803d-f791-454d-9e3d-cf8ce9ce0da0
-- title:
--   Iterate planar edge augmentation to the triangulation count
-- statement:
--   If every planar graph on this vertex type below the 3|V|−6 edge threshold admits a planar one-edge extension, then any such starting graph can be extended to exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_from_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hAug : ∀ (G : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G →
      G.edgeSet.ncard + 6 < 3 * Fintype.card V →
      ∃ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet ⊆ H.edgeSet ∧ H.edgeSet.ncard = G.edgeSet.ncard + 1) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
