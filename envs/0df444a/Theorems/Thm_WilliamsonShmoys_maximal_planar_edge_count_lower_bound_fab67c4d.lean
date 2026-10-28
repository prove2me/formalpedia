-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fab67c4d
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fab67c4d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:03:58.947285+00:00
-- url     : https://prove2.me/theorems/04e7fc1d-f6a3-4470-99a7-3bdacc11329f
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable graph on at least three vertices with no drawable strict edge supergraph on those vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fab67c4d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L.edgeSet ⊂ M.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn M) :
    3 * (Fintype.card V : Int) - 6 ≤ (L.edgeSet.ncard : Int) := by sorry
