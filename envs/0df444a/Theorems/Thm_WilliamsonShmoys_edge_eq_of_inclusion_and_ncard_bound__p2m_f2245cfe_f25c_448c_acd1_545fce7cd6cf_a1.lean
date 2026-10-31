-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_eq_of_inclusion_and_ncard_bound__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
-- name    : WilliamsonShmoys.edge_eq_of_inclusion_and_ncard_bound__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:40.898826+00:00
-- url     : https://prove2.me/theorems/15b389eb-111b-43c9-8690-22145e044bf7
-- title:
--   Graph inclusion and edge-count bound force equality
-- statement:
--   For finite graphs on the same vertex type, if G is a subgraph of H and H has no more edges than G, then the graphs are equal. The proof route is finite-set inclusion plus cardinality antisymmetry, followed by graph extensionality. This handles equality of edge counts directly and preserves the inclusion hypothesis needed to conclude graph equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_eq_of_inclusion_and_ncard_bound__p2m_f2245cfe_f25c_448c_acd1_545fce7cd6cf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) : H = G := by sorry
