-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_subgraph_1794ae85
-- name    : WilliamsonShmoys.edge_count_mono_of_subgraph_1794ae85
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:31:45.035985+00:00
-- url     : https://prove2.me/theorems/a4c99e08-aa13-4fee-b777-d1c612c3e118
-- title:
--   Edge count is monotone under subgraphs
-- statement:
--   For finite graphs on the same vertex type, subgraph inclusion implies edge-count monotonicity. This transfers the connected supergraph’s bound back to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_of_subgraph_1794ae85
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
