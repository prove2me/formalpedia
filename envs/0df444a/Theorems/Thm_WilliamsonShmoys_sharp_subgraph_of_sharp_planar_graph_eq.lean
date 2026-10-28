-- Prove2me | Theorems.Thm_WilliamsonShmoys_sharp_subgraph_of_sharp_planar_graph_eq
-- name    : WilliamsonShmoys.sharp_subgraph_of_sharp_planar_graph_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:00:50.256037+00:00
-- url     : https://prove2.me/theorems/8d2a953e-ff9e-432a-b768-9752aab7bd7a
-- title:
--   A sharp subgraph of a sharp graph is equal to it
-- statement:
--   For finite graphs on the same vertex type, if one is a subgraph of the other and both have the same sharp edge count, then they are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.sharp_subgraph_of_sharp_planar_graph_eq
    {V : Type} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hH : H.edgeSet.ncard + 6 = 3 * Fintype.card V)
    (hK : K.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    H = K := by sorry
