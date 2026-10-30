-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_ac816c5dcb924d25
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_ac816c5dcb924d25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:05:13.318+00:00
-- url     : https://prove2.me/theorems/dbc93b00-aa6f-4c67-84c3-d39e54fa7144
-- title:
--   Simple planar edge bound from a drawing
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3v − 6 edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_ac816c5dcb924d25
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
