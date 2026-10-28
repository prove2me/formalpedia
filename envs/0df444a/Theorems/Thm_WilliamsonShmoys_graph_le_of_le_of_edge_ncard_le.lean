-- Prove2me | Theorems.Thm_WilliamsonShmoys_graph_le_of_le_of_edge_ncard_le
-- name    : WilliamsonShmoys.graph_le_of_le_of_edge_ncard_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:27:08.933715+00:00
-- url     : https://prove2.me/theorems/b74ce28f-4d43-4ff7-867b-06fd07849a56
-- title:
--   Edge inclusion and a reverse edge-set cardinality bound imply reverse inclusion
-- statement:
--   For finite simple graphs on the same vertex type, if `M` is a subgraph of `N` and `N` has no more edges, then `N` is a subgraph of `M`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.graph_le_of_le_of_edge_ncard_le
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hcard : N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    N ≤ M := by sorry
