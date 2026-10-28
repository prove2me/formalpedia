-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_can_be_augmented_of_edge_card_lt
-- name    : WilliamsonShmoys.planar_graph_can_be_augmented_of_edge_card_lt
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T14:02:15.798993+00:00
-- url     : https://prove2.me/theorems/1a301c0e-00f6-408b-902b-43a2d6d3ebd1
-- title:
--   Augmenting a planar graph below the maximal edge count
-- statement:
--   Every simply drawn planar graph on at least three vertices with fewer than 3|V|−6 edges has a strictly larger planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_can_be_augmented_of_edge_card_lt
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : P.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := by sorry
