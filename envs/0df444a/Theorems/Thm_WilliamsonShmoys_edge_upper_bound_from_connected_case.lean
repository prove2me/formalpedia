-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_upper_bound_from_connected_case
-- name    : WilliamsonShmoys.edge_upper_bound_from_connected_case
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:31:45.453296+00:00
-- url     : https://prove2.me/theorems/e8da4cf9-d0ff-4561-8805-4ee8ceacc76e
-- title:
--   Reduce the planar edge bound to connected graphs
-- statement:
--   The bound for a finite graph with at least three vertices follows from the connected case by restricting the drawing to components and summing their edge bounds. Singleton components contribute zero edges; components of size two contribute at most one edge. The resulting component-count inequality must retain the parent's total size lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_upper_bound_from_connected_case
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V)
    (hConnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (H : SimpleGraph W), H.Connected → HasPlanarDrawingOn H →
      3 <= Fintype.card W →
      (H.edgeSet.ncard : Int) <= 3 * (Fintype.card W : Int) - 6) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  sorry
