-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_strict_of_new_edge
-- name    : WilliamsonShmoys.edge_count_strict_of_new_edge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:25:11.595981+00:00
-- url     : https://prove2.me/theorems/a6211908-52ba-44de-81a6-67653067e02c
-- title:
--   A newly added edge strictly increases edge count
-- statement:
--   For finite vertex types, a supergraph containing an edge between vertices that were not reachable in the original graph has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_strict_of_new_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (u v : V)
    (hHK : H ≤ K)
    (hSeparated : ¬ H.Reachable u v)
    (hNew : K.Adj u v) :
    H.edgeSet.ncard < K.edgeSet.ncard := by sorry
