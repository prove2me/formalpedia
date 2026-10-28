-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_88511758
-- name    : WilliamsonShmoys.planar_edge_count_lower_88511758
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:36:13.277035+00:00
-- url     : https://prove2.me/theorems/57e9d048-3bef-4fbc-b0cb-15716802cae0
-- title:
--   Connected graphs have at least one fewer edge than vertices
-- statement:
--   Every finite connected simple graph has at least |V| − 1 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_lower_88511758
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 := by sorry
