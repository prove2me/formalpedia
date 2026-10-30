-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound_maximal_edge_count_562a75e6
-- name    : WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_edge_count_562a75e6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:12:09.38206+00:00
-- url     : https://prove2.me/theorems/7607aed3-a244-45f9-bed7-d65cb2c30861
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A finite connected drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_count_upper_bound_maximal_edge_count_562a75e6
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (H.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
