-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:52:55.461983+00:00
-- url     : https://prove2.me/theorems/ecc5a45b-5935-4e7b-925e-c28bb1f6cba9
-- title:
--   Edge count of a connected edge-maximal planar graph
-- statement:
--   A connected edge-maximal planar simple graph on at least three vertices has exactly three times its vertex count minus six edges. The vertex bound ensures the natural-number subtraction is in the usual Euler-formula range.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hmax : ∀ G : SimpleGraph V,
      H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
