-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_retry_2cbac039_augment
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039_augment
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:52:16.223827+00:00
-- url     : https://prove2.me/theorems/d831683a-dc67-4372-b92f-31061460229f
-- title:
--   Sparse planar graphs admit a drawable edge augmentation
-- statement:
--   Any drawable finite simple graph with at least three vertices and fewer than 3n−6 edges has a drawable strict supergraph on the same vertex type. This removes the maximality premise from the target and provides the contradiction needed for the parent proof. Boundary cases include disconnected graphs and the three-vertex case; the strict sparsity hypothesis excludes graphs already at the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039_augment
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hSparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeSet ⊂ M.edgeSet := by sorry
