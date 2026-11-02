-- Prove2me | Theorems.Thm_WilliamsonShmoys_graph_eq_of_le_and_ncard__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
-- name    : WilliamsonShmoys.graph_eq_of_le_and_ncard__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:10:38.705375+00:00
-- url     : https://prove2.me/theorems/2aeb5130-3084-4ed9-bb5a-0da23ff8dba1
-- title:
--   Inclusion and edge count determine a finite graph
-- statement:
--   If one simple graph on a finite vertex type is a subgraph of another and has at least as many edges, then the graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.graph_eq_of_le_and_ncard__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
    {V : Type} [Fintype V]
    {L M : SimpleGraph V}
    (hLM : L ≤ M) (hcard : M.edgeSet.ncard ≤ L.edgeSet.ncard) : M = L := by sorry
