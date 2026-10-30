-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_augmentation_for_maximal_face_decomposition_6274f47d
-- name    : WilliamsonShmoys.planar_graph_edge_augmentation_for_maximal_face_decomposition_6274f47d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:37:10.286165+00:00
-- url     : https://prove2.me/theorems/9bfcd617-f846-4378-a6d8-859a6c446614
-- title:
--   Augmenting a planar graph below the maximal edge count
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than `3n − 6` edges, it has a drawable strict supergraph on the same vertices. The strict edge-set inclusion is essential: maximality then contradicts this child directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_augmentation_for_maximal_face_decomposition_6274f47d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSmall : L.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊂ M.edgeSet ∧ HasPlanarDrawingOn M := by sorry
