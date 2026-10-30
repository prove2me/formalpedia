-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_with_fewer_edges_can_be_augmented
-- name    : WilliamsonShmoys.planar_graph_with_fewer_edges_can_be_augmented
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:57:42.457019+00:00
-- url     : https://prove2.me/theorems/75c1b2f2-facf-4eef-8da2-251652dc40f8
-- title:
--   Augmenting an underfull planar graph
-- statement:
--   A graph with the supplied planar drawing on at least three vertices and strictly fewer than 3n − 6 edges has a proper planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_with_fewer_edges_can_be_augmented
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hLow : N.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ Q : SimpleGraph V,
      N ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q ≠ N := by
  sorry
