-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound_20261028
-- name    : WilliamsonShmoys.planar_maximal_edge_lower_bound_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:21:29.356783+00:00
-- url     : https://prove2.me/theorems/e7809764-4dde-4cb5-94b3-f6ddb89cb84c
-- title:
--   Maximal drawable graphs satisfy the planar edge lower bound
-- statement:
--   An inclusion-maximal graph admitting the supplied planar drawing, on at least three vertices, has at least \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_lower_bound_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
