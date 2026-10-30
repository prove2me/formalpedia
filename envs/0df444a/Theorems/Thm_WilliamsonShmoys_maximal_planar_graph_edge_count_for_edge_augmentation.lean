-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_edge_augmentation
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_for_edge_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:40:03.831108+00:00
-- url     : https://prove2.me/theorems/8fa97b2b-c7b7-43d6-b65e-97868f5ed033
-- title:
--   Edge count of a maximal planar graph for edge augmentation
-- statement:
--   A graph with a planar drawing on at least three vertices, with no strictly larger planar supergraph on those vertices, has exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_for_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M.edgeSet ⊂ N.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn N) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
