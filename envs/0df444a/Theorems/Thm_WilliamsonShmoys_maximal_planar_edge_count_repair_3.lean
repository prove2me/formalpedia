-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair_3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_repair_3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:45:17.420999+00:00
-- url     : https://prove2.me/theorems/2202ea51-1581-4406-aef5-84bf04e75de3
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3n−6 edges. The planar embedding argument that maximality forces triangular faces, followed by Euler's formula, remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_repair_3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
