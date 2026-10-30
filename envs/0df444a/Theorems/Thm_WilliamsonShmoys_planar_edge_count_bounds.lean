-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bounds
-- name    : WilliamsonShmoys.planar_edge_count_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:21:24.640658+00:00
-- url     : https://prove2.me/theorems/88511758-727f-4cc9-a7e6-ce8c14ee59a0
-- title:
--   Edge count bounds for a connected planar graph
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free drawing has at least |V|−1 edges and at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 ∧
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
