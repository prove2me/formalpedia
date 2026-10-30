-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3_maximal_edge_bound
-- name    : WilliamsonShmoys.edge_count_planar_upper_retry3_maximal_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T14:07:12.855308+00:00
-- url     : https://prove2.me/theorems/2565dbbd-2d73-4c37-a634-4dae56689365
-- title:
--   Euler edge bound for an edge-maximal planar drawing
-- statement:
--   An edge-maximal graph with the supplied crossing-free drawing and at least three vertices satisfies the planar Euler edge bound. The three-vertex lower bound is needed for the usual triangulation argument; no connectedness hypothesis is assumed, since maximality must first rule out disconnected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_planar_upper_retry3_maximal_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
