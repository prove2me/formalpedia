-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_88511758
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_88511758
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:36:39.995542+00:00
-- url     : https://prove2.me/theorems/6357fee1-f927-4c5b-a160-dca513168a22
-- title:
--   Upper edge bound for a connected graph with a planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free drawing has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_88511758
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
