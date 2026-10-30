-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_via_euler
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_via_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:17:10.311251+00:00
-- url     : https://prove2.me/theorems/125b15c2-a985-4e65-866d-b1ba0191aeb0
-- title:
--   A maximal drawable graph meets the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_via_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      (∀ ⦃u v⦄, M.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
