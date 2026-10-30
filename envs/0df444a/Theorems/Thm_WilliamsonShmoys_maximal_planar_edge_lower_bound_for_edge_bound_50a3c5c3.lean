-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_edge_bound_50a3c5c3
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_for_edge_bound_50a3c5c3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:02:10.762602+00:00
-- url     : https://prove2.me/theorems/2544328d-c546-40a4-b62c-2962333b2b8b
-- title:
--   Maximal planar edge lower bound for the edge-count theorem
-- statement:
--   A drawable graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex set has at least `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_for_edge_bound_50a3c5c3
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V)
    (hQmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q) :
    3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by sorry
