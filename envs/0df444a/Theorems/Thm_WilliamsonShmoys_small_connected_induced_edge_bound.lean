-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_connected_induced_edge_bound
-- name    : WilliamsonShmoys.small_connected_induced_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:34:17.503053+00:00
-- url     : https://prove2.me/theorems/4b9e51ca-5528-4384-a18b-8dd7c8ca8290
-- title:
--   Bound edges in a connected induced subgraph with fewer than three vertices
-- statement:
--   A nonempty set of fewer than three vertices has cardinality one or two. Its induced simple graph has at most zero or one edge, respectively, which is below the requested bound. This handles the small-size branch independently of the local hypothesis; the proof route is a cardinality case split and the simple-graph edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_connected_induced_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hsmall : C.card < 3) :
    (G.induce (fun v => v ∈ C)).edgeSet.ncard ≤ 3 * C.card - 3 := by sorry
