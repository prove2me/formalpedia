-- Prove2me | Theorems.Thm_WilliamsonShmoys_supergraph_connected_edge_count_9064c577
-- name    : WilliamsonShmoys.supergraph_connected_edge_count_9064c577
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:52:37.143446+00:00
-- url     : https://prove2.me/theorems/07253e9a-1a0b-43e6-8ccc-83d35c4646f6
-- title:
--   Connectivity and edge count for supergraphs
-- statement:
--   A supergraph of a connected finite graph is connected and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.supergraph_connected_edge_count_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hConn : H.Connected)
    (hHK : ∀ ⦃u v⦄, H.Adj u v → K.Adj u v) :
    K.Connected ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
