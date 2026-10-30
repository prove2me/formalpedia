-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:42:58.111261+00:00
-- url     : https://prove2.me/theorems/440ea11e-1d77-43d1-af5c-4e2a62fa968d
-- title:
--   Edge bound for a maximal planar graph
-- statement:
--   A graph on at least three vertices that is maximal among graphs admitting a crossing-free drawing has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
