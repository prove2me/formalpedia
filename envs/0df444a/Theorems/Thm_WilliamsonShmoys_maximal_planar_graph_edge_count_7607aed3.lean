-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_7607aed3
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_7607aed3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:09:36.472008+00:00
-- url     : https://prove2.me/theorems/557d411c-1251-4e2b-aaca-59bc1f302080
-- title:
--   Edge count of a maximal planar graph for triangulation
-- statement:
--   A connected inclusion-maximal drawable simple graph on at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_7607aed3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
