-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card_lower_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_card_lower_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:00.325201+00:00
-- url     : https://prove2.me/theorems/57c283a7-68a4-4e3d-813f-6e392f4dfebc
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph maximal under drawable supergraphs, with at least three vertices, has at least 3|V| − 6 edges. This removes the maximality and triangulation argument from the parent; prove it by showing that any non-triangular face permits adding a missing edge while preserving the drawing, then apply Euler’s formula to the resulting triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_card_lower_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by sorry
