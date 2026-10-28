-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_augmentation_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- name    : WilliamsonShmoys.maximal_planar_graph_augmentation_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:02:39.391185+00:00
-- url     : https://prove2.me/theorems/8a5c5037-77da-430d-9643-dec01e9a1ed1
-- title:
--   Augment a planar drawing to meet the planar edge bound
-- statement:
--   Any graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on the same vertices with at least 3|V|−6 edges. The parent uses maximality to show this supergraph has exactly the original edge set, then transfers the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_augmentation_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
